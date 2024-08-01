package cypher.algebra.translator;

import cypher.algebra.HyperTuple;
import cypher.ast.clause.projection.Limit;
import cypher.ast.clause.projection.SortItem;
import cypher.ast.expression.*;
import cypher.err.CypherUExprTranslationError;
import cypher.translate.Cypher2UExpr;
import cypher.translate.Cypher2UExprHelper;
import org.apache.commons.lang3.tuple.Pair;
import representations.GraphAlgebra;
import representations.graphalgebra.*;
import sqlsolver.liastar.Liastar;
import sqlsolver.uexpr.*;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;
import java.util.*;

import static sqlsolver.uexpr.UExprSupport.mkNotNullPred;
import static sqlsolver.uexpr.UPred.PredKind.EQ;

public class GraphAlgebraTranslator {
    GraphAlgebra algebra;
    Cypher2UExpr exprTranslator = new Cypher2UExpr(this);

    List<HyperTuple> hyperTuples = new ArrayList<>();

    public static boolean peel = false;
    public static UVar outVar;

    UTerm body;
    public Set<UVar> sumBounds = new HashSet<>();

    Set<UVar> solidVars = new HashSet<>();

    Set<UVar> optionalVars = new HashSet<>();

    boolean solidPattern = true;

    public GraphAlgebraTranslator(GraphAlgebra algebra) {
        this.algebra = algebra;
    }

    public UTerm translate() {
        if (outVar == null) {
            outVar = UVar.mkBase(UName.mk("t"));
        }
        return translateAlgebra(algebra);
    }

    private UTerm translateAlgebra(GraphAlgebra algebra) {
        if (algebra == null) {
            return null;
        }
        switch (algebra.kind()) {
            case UNION -> {
                return translateUnion(((Union) algebra));
            }
            case BAG_UNION -> {
                return translateBagUnion(((BUnion) algebra));
            }
            case NATURE_JOIN -> {
                return translateJoin(((Join) algebra));
            }
            case LEFT_OUTER_JOIN -> {
                return translateLOJ(((LOJoin) algebra));
            }
            case PROJ -> {
                return translateProj(((Projection) algebra));
            }
            case GRAPH_PATTERN_PART -> {
                return translateGraph(((GraphPatternPart) algebra));
            }
            case SELECTION -> {
                return translateSelection(((Selection) algebra));
            }
            case UNWIND -> {
                return translateUnwind(((UnwindAlge) algebra));
            }
            case EMPTY_SET -> {
                return null;
            }
            case SORT -> {
                return translateSort(((Sort) algebra));
            }
            case TOP -> {
                return translateTop(((Top) algebra));
            }
            case DEDUP -> {
                return translateDedup(((Dedup) algebra));
            }
        }
        return null;
    }

    private UTerm translateDedup(Dedup algebra) {
        return USquash.mk(translateAlgebra(algebra.algebra));
    }

    private UTerm translateSort(Sort sort) {
        UTerm body = translateAlgebra(sort.algebra);
        List<UTerm> orders = new ArrayList<>();
        for (int i = 0; i < sort.sortItems.size(); i++) {
            SortItem item = sort.sortItems.get(i);
            String asc = item instanceof SortItem.Asc ? "ASC" : "DSC";
            UVar orderProj = UVar.mkProj(UName.mk(asc), outVar);
            UTerm order = UPred.mkBinary(EQ, UVarTerm.mk(orderProj), exprTranslator.translateExpr(item.expression));
            orders.add(order);
        }
        return UMul.mk(UAdd.mk(orders), body);
    }

    private UTerm translateTop(Top top) {
        Limit limit = top.limit;
        ScriptEngineManager manager = new ScriptEngineManager();
        ScriptEngine engine = manager.getEngineByName("JavaScript");
        try {
            String result = String.valueOf(engine.eval(limit.expression.toString()));
            UVar orderProj = UVar.mkProj(UName.mk("limit"), outVar);
            UTerm eq = UPred.mkBinary(EQ, UVarTerm.mk(orderProj), UConst.mk(Integer.parseInt(result)));
            return UMul.mk(eq, translateAlgebra(top.algebra));
        } catch (ScriptException e) {
            e.printStackTrace();
            return null;
        }
    }

    private Map<UVar, UTerm> constMap = new HashMap<>();
    private UTerm translateUnwind(UnwindAlge unwind) {
        UTerm body = translateAlgebra(unwind.sub);
        Variable alias = unwind.alias;
        if (alias.linked.isConstList()) {
            List<UTerm> listTerms = new ArrayList<>();
            List<Expression> exprs = ((ListExpression) alias.linked).exprs;
            if (exprs.isEmpty()) {
                UTerm term = UConst.zero();
                listTerms.add(term);
            }
            for (Expression expr : exprs) {
                MapExpression map = ((MapExpression) expr);
                int colIndex = 1;
                List<UTerm> rowTerm = new ArrayList<>();
                for (Pair<PropertyKeyName, Expression> col : map.props) {
                    String colName = "c" + colIndex;
                    Expression value = col.getRight();
                    assert value instanceof Literal;
                    UVar colVar = UVar.mkProj(UName.mk(colName), UVar.mkBase(UName.mk(alias.name)));
                    UTerm term = UPred.mkBinary(EQ, UVarTerm.mk(colVar), exprTranslator.translateExpr(value));
                    constMap.put(colVar, term);
                    rowTerm.add(term);
                    colIndex++;
                }
                listTerms.add(UMul.mk(rowTerm));
            }
            return UMul.mk(body, UAdd.mk(listTerms));
        }
        alias.kind = Variable.VarKind.BASE;
        return body;
    }

    private UTerm translateGraph(GraphPatternPart patternPart) {
        if (patternPart.patternKind() == GraphPatternPart.PatternKind.RELATIONSHIP) {
            return translateExpand(((Expand) patternPart));
        }
        if (patternPart.patternKind() == GraphPatternPart.PatternKind.NODE) {
            return translateNode(((Node) patternPart));
        }
        throw new CypherUExprTranslationError("GraphPatternPart type error");
    }

    private Variable getLinked(Variable variable) {
        while (variable.linked != null) {
            if (variable.linked instanceof Variable) {
                variable = ((Variable) variable.linked);
            } else
                break;
        }
        return variable;
    }

    private UTerm translateNode(Node node) {
        node.var = getLinked(node.var);
        UVar nVar = UVar.mkBase(UName.mk(node.var.name));
        sumBounds.add(nVar);
        if (solidPattern) {
            solidVars.add(nVar);
        } else {
            if (!solidVars.contains(nVar)) {
                optionalVars.add(nVar);
            }
        }
        UTerm n = Cypher2UExprHelper.node(nVar);
        List<UTerm> labels = new ArrayList<>();
        for (String type : node.labels) {
            labels.add(Cypher2UExprHelper.label(nVar, type));
        }
        if (!labels.isEmpty())
            n = UMul.mk(n, UAdd.mk(labels));
        if (node.constraint != null) {
            UTerm cond = exprTranslator.translateExpr(node.constraint);
            n = UMul.mk(n, cond);
        }
        return n;
    }

    private UTerm translateExpand(Expand expand) {
        expand.var = getLinked(expand.var);
        UVar var = UVar.mkBase(UName.mk(expand.var.name));
        UTerm rel = Cypher2UExprHelper.rel(var);
        UTerm right = translateAlgebra(expand.end);
        UTerm left = translateAlgebra(expand.start);
        UVar leftEnd = UVar.mkBase(UName.mk(expand.start.var.name));
        UVar rightEnd = UVar.mkBase(UName.mk(expand.end.var.name));
        sumBounds.add(var);
        if (solidPattern) {
            solidVars.add(var);
        } else {
            if (!solidVars.contains(var)) {
                optionalVars.add(var);
            }
        }
//        sumBounds.remove(leftEnd);
//        sumBounds.remove(rightEnd);
        UTerm out;
        UTerm in;
        if (expand.getDirection() == Expand.Direction.OUT) {
            out = UPred.mkBinary(UPred.PredKind.EQ, leftEnd, Cypher2UExprHelper.relIn(var));
            in = UPred.mkBinary(UPred.PredKind.EQ, rightEnd, Cypher2UExprHelper.relOut(var));
        } else {
            out = UPred.mkBinary(UPred.PredKind.EQ, rightEnd, Cypher2UExprHelper.relIn(var));
            in = UPred.mkBinary(UPred.PredKind.EQ, leftEnd, Cypher2UExprHelper.relOut(var));
        }
        rel = UMul.mk(rel, out, in);
        List<UTerm> types = new ArrayList<>();
        for (String type : expand.labels) {
            types.add(Cypher2UExprHelper.label(var, type));
        }
        if (!types.isEmpty())
            rel = UMul.mk(rel, UAdd.mk(types));
        if (expand.constraint != null) {
            UTerm cond = exprTranslator.translateExpr(expand.constraint);
            rel = UMul.mk(rel, cond);
        }
        UTerm inner = translateAlgebra(expand.algebra);
        return UMul.mk(left, rel, right, inner);
    }

    // (Node(x8) * Rel(x9) * [x1 = in(x9)] * [x8 = out(x9)] * Node(x1) * Rel(x2) * [x1 = in(x2)] * [x3 = out(x2)] * Node(x3) * Rel(x4) * [x5 = in(x4)] * [x3 = out(x4)] * Node(x5) * Node(x6) * Rel(x7) * [x6 = in(x7)] * [x8 = out(x7)] * [Person(x5) = 1] * [name(x5) = '"Tom Hanks"'] * [ACTED_IN(x4) = 1] * [ACTED_IN(x2) = 1] * [ACTED_IN(x9) = 1] * [Person(x6) = 1] * [name(x6) = '"Tom Cruise"'] * [ACTED_IN(x7) = 1] * [queryTuple = name(x1)])||
    private UTerm translateBagUnion(BUnion bagUnion) {
        UTerm left = translateAlgebra(bagUnion.left);
        UTerm right = translateAlgebra(bagUnion.right);
        return UAdd.mk(left, right);
    }

    private UTerm translateUnion(Union union) {
        UTerm left = translateAlgebra(union.left);
        UTerm right = translateAlgebra(union.right);
        return USquash.mk(UAdd.mk(left, right));
    }

    private UTerm translateLOJ(LOJoin loJoin) {
        GraphAlgebra left = loJoin.left;
        GraphAlgebra right = loJoin.right;
        UTerm lTerm = translateAlgebra(left);
        solidPattern = false;
        UTerm rTerm = translateAlgebra(right);
        solidPattern = true;
        if (!optionalVars.isEmpty())
            rTerm = USum.mk(optionalVars, rTerm);
        UTerm absenceCond = UNeg.mk(rTerm.copy());
        for (UVar var : optionalVars) {
            absenceCond.replaceVar(var, UVar.mkBase(UName.mk(Liastar.newVarName())), true);
            absenceCond = UMul.mk(absenceCond, UExprSupport.mkIsNullPred(var));
        }
        rTerm = UAdd.mk(rTerm, absenceCond);
        if (lTerm != null) {
            return UMul.mk(lTerm, rTerm);
        } else {
            return rTerm;
        }
    }

    private UTerm translateJoin(Join join) {
        UTerm left = translateAlgebra(join.left);
        UTerm right = translateAlgebra(join.right);
        return UMul.mk(left, right);
    }

    private UTerm translateSelection(Selection selection) {
        UTerm term = translateAlgebra(selection.relation);
        UTerm term1 = exprTranslator.translateExpr(selection.pred);
        return UMul.mk(term, term1);
    }

    private UTerm translateProj(Projection projection) {
        UTerm body = translateAlgebra(projection.relation);
        this.body = body;
        List<UTerm> retTerms = new ArrayList<>();
        for (int i = 0; i < projection.projs.size(); i++) {
            ProjOp op = projection.projs.get(i);
            UTerm retExpr = null;
            if (projection.isOuter()) {
                UTerm outTerm = UVarTerm.mk(UVar.mkProj(UName.mk("#" + (i + 1)), outVar));
                Cypher2UExpr.outTerm = outTerm;
                if (op.kind() == ProjOp.ProjKind.RENAME) {
                    Expression ret = ((Rename) op).expr;
                    Variable var = ((Rename) op).alias;
                    try {
                        UTerm src = exprTranslator.translateExpr(ret);
                        UTerm tgt = UVarTerm.mk(UVar.mkBase(UName.mk(var.name)));
//                    retTerms.add(alias);
                        if (ret.isAggExpression()) {
                            retExpr = translateAgg(outTerm, ret);
                            retTerms.add(retExpr);
                            continue;
                        } else
                            retExpr = exprTranslator.translateExpr(ret);
                    } catch (RuntimeException runtimeException) {

                    }
                }
                if (op.kind() == ProjOp.ProjKind.EXPR) {
                    Expression ret = ((ProjExpr) op).expr;
                    if (ret instanceof Literal.Null) {
                        ret = new Unary.IsNull(new Property(new Variable(outVar.name().toString()), new PropertyKeyName("#" + (i + 1))));
                        retExpr = exprTranslator.translateExpr(ret);
                        Cypher2UExpr.completed = true;
                    }
                    else if (ret.isAggExpression()) {
                        retExpr = translateAgg(outTerm, ret);
                        retTerms.add(retExpr);
                        continue;
                    } else
                        retExpr = exprTranslator.translateExpr(ret);
                }
                if(!Cypher2UExpr.completed)
                    retTerms.add(UPred.mkBinary(
                            EQ,
                            outTerm,
                            retExpr
                    ));
                else {
                    Cypher2UExpr.completed = false;
                    retTerms.add(retExpr);
                }
            }
        }
        UTerm proj;
        if (body == null) {
            proj = UMul.mk(retTerms);
        } else {
            proj = UMul.mk(body, retTerms);
        }
        if (projection.isOuter() && (sumBounds.size()>1 || peel)) {
            UTerm sum = USum.mk(new HashSet<>(sumBounds), proj);
            sumBounds.clear();
            return sum;
        } else {
            return proj;
        }
    }

    public UTerm translateAgg(UTerm tr, Expression aggExpr) {
        if (aggExpr instanceof Binary.Multiply multiply) {
            return UMul.mk(translateAgg(tr, multiply.lhs), translateAgg(tr, multiply.rhs));
        } else if (aggExpr instanceof Binary.Divide div) {
            return UFunc.mk(
                    UFunc.FuncKind.INTEGER, UName.mk("divide"),
                    Arrays.asList(translateAgg(tr, div.lhs), translateAgg(tr, div.rhs)));
        } else if (aggExpr instanceof Binary.Add add) {
            return UAdd.mk(translateAgg(tr, add.lhs), translateAgg(tr, add.rhs));
        } else if (aggExpr instanceof Binary.Subtract sub) {
            return UFunc.mk(
                    UFunc.FuncKind.INTEGER, UName.mk("minus"),
                    Arrays.asList(translateAgg(tr, sub.lhs), translateAgg(tr, sub.rhs)));
        } else {
            FunctionInvocation func = ((FunctionInvocation) aggExpr);
            Expression arg = func.args.get(0);
            if (arg instanceof Variable variable && variable.linked != null) {
                arg = variable.linked;
            }
            if (arg instanceof FunctionInvocation functionInvocation) {
                functionInvocation.distinct = true;
                return translateAgg(tr, functionInvocation);
            }
            if (func.functionName.name.equals("COUNT")) {
                UTerm cond = body.copy();
                if (!arg.toString().equals("*")) {
                    UVar agg;
                    if (arg instanceof Variable) {
                        agg = UVar.mkBase(UName.mk(((Variable) arg).name));
                    } else {
                        if (arg instanceof ListExpression listExpression) {
                            return UConst.mk(listExpression.exprs.size());
                        }
                        assert arg instanceof Property || (arg instanceof Variable && ((Variable) arg).linked instanceof Property);
                        if (!(arg instanceof Property)) {
                            arg = ((Property) ((Variable) arg).linked);
                        }
                        UVar map = UVar.mkBase(UName.mk(((Variable) ((Property) arg).map).name));
                        agg = UVar.mkProj(UName.mk(((Property) arg).propertyKey.name), map);
                    }
                    if (func.distinct) {

                    }
                    if (cond instanceof USum sum) {
                        sum.addMulSubTerm(mkNotNullPred(agg));
                    } else {
                        cond = UMul.mk(UPred.mkBinary(EQ, UVarTerm.mk(agg), tr), mkNotNullPred(agg));
                        cond = USum.mk(sumBounds, cond).copy();
                    }
                } else {
                    System.out.println();
                }
                cond = UMul.mk(UPred.mkBinary(EQ, cond, tr));
                cond = exprTranslator.replaceAllBoundedVars(cond);
                return cond;
            } else if (func.functionName.name.equals("SUM")) {
                UTerm cond = body.copy();
                UVar agg;
                if (arg instanceof Variable variable) {
                    agg = UVar.mkBase(UName.mk(variable.name));
                } else {
                    assert arg instanceof Property;
                    assert ((Property) arg).map instanceof Variable;
                    UVar map = UVar.mkBase(UName.mk(((Variable) ((Property) arg).map).name));
                    agg = UVar.mkProj(UName.mk(((Property) arg).propertyKey.name), map);
                }
                if (func.distinct) {

                }
                UTerm sumTerm = UMul.mk(mkNotNullPred(agg), UVarTerm.mk(agg), UPred.mkBinary(EQ, UVarTerm.mk(agg), tr));
                if (cond instanceof USum sum) {
                    sum.addMulSubTerm(sumTerm);
                } else {
                    cond = UMul.mk(cond, sumTerm);
                }
                cond = UMul.mk(UPred.mkBinary(EQ, cond, tr));
                cond = exprTranslator.replaceAllBoundedVars(cond);
                return cond;
            } else if (func.functionName.name.equals("AVG")) {
                FunctionInvocation SUM = func.copy();
                FunctionInvocation COUNT = new FunctionInvocation(new FunctionName("COUNT"),false,
                        List.of(new Literal.Star()));
                SUM.functionName.name = "SUM";
                COUNT.functionName.name = "COUNT";
                UTerm sumTerm = translateAgg(tr, SUM);
                UTerm cntTerm = translateAgg(tr, COUNT);
                return UFunc.mk(UFunc.FuncKind.INTEGER, UName.mk("divide"), Arrays.asList(sumTerm,cntTerm));
//                return UPred.mkBinary(EQ,
//                        UMul.mk(tr, cntTerm),
//                        sumTerm
//                );
            } else if (func.functionName.name.equals("MAX")) {
                if (func.isLiteralFunc()) {
                    return UPred.mkBinary(EQ, exprTranslator.parseExpr2UTerm(func.args.get(0)), tr);
                }
                UTerm cond1 = body.copy();
                UTerm cond2 = body.copy();
                if (arg instanceof Literal.Integer integer) {
                    return UConst.mk((int) integer.value);
                }
                assert ((Property) arg).map instanceof Variable;
                UVar map = UVar.mkBase(UName.mk(((Variable) ((Property) arg).map).name));
                UVar agg = UVar.mkProj(UName.mk(((Property) arg).propertyKey.name), map);
                UTerm subCond1 = UPred.mkBinary(UPred.PredKind.GT, UVarTerm.mk(agg), tr);
                UTerm subCond2 = UPred.mkBinary(EQ, UVarTerm.mk(agg), tr);
                if (cond1 instanceof USum sum) {
                    sum.addMulSubTerm(subCond1);
                } else {
                    cond1 = UMul.mk(cond1, subCond1);
                }
                if (cond2 instanceof USum sum) {
                    sum.addMulSubTerm(subCond2);
                } else {
                    cond2 = UMul.mk(cond2, subCond2);
                }
                System.err.println(cond1);
                System.err.println(cond2);
                cond1 = exprTranslator.replaceAllBoundedVars(cond1);
                cond2 = exprTranslator.replaceAllBoundedVars(cond2);
                UTerm cond = UMul.mk(UNeg.mk(cond1), USquash.mk(cond2));
                cond = UMul.mk(UPred.mkBinary(EQ, cond, tr));
                return cond;
            } else if (func.functionName.name.equals("MIN")) {
                UTerm cond1 = body.copy();
                UTerm cond2 = body.copy();
                assert arg instanceof Property;
                assert ((Property) arg).map instanceof Variable;
                UVar map = UVar.mkBase(UName.mk(((Variable) ((Property) arg).map).name));
                UVar agg = UVar.mkProj(UName.mk(((Property) arg).propertyKey.name), map);
                UTerm subCond1 = UPred.mkBinary(UPred.PredKind.LT, UVarTerm.mk(agg), tr);
                UTerm subCond2 = UPred.mkBinary(EQ, UVarTerm.mk(agg), tr);
                if (cond1 instanceof USum sum) {
                    sum.addMulSubTerm(subCond1);
                } else {
                    cond1 = UMul.mk(cond1, subCond1);
                }
                if (cond2 instanceof USum sum) {
                    sum.addMulSubTerm(subCond2);
                } else {
                    cond2 = UMul.mk(cond2, subCond2);
                }
                System.err.println(cond1);
                System.err.println(cond2);
                cond1 = exprTranslator.replaceAllBoundedVars(cond1);
                cond2 = exprTranslator.replaceAllBoundedVars(cond2);
                UTerm cond = UMul.mk(UNeg.mk(cond1), USquash.mk(cond2));
                cond = UMul.mk(UPred.mkBinary(EQ, cond, tr));
                return cond;
            }
        }
        return null;
    }
}
