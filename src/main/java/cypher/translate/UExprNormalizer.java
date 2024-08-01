package cypher.translate;

import sqlsolver.common.NaturalCongruence;
import sqlsolver.liastar.Liastar;
import sqlsolver.uexpr.*;

import java.util.*;
import java.util.function.Function;

import static sqlsolver.common.IterableSupport.any;
import static sqlsolver.common.IterableSupport.linearFind;
import static sqlsolver.common.ListSupport.filter;
import static sqlsolver.uexpr.UExprSupport.*;
import static sqlsolver.uexpr.UKind.*;
import static sqlsolver.uexpr.UPred.PredKind.EQ;

public class UExprNormalizer {
    public boolean isModified;
    public static UTerm globalExpr;

    public UTerm normalizeTerm(UTerm expr) {
        do {
            globalExpr = expr;
            isModified = false;
//            expr = removeSumEqPred(expr);
            expr = removeDuplicatePatternPartVar(expr);
            expr = removeUselessSquashSumFromSumBody(expr);
            expr = removeUnusedSummationBoundedVar(expr);
            expr = removeIsNullPredOnValue(expr);
            expr = simplifyInequalityByCongruence(expr);
//            expr = removeUselessSquash(expr);
        } while (isModified);
        return expr;
    }

//    private UTerm removeUselessSquash(UTerm term) {
//
//        term = transformSubTerms(term, this::removeUselessSquash);
//        if (term.kind() != SQUASH)
//            return term;
//        USquash expr = (USquash) term;
//        UTerm body = expr.body();
//        if (!(body instanceof UMul))
//            return expr;
//        ArrayList<UTerm> subTerms = new ArrayList<>();
//        subTerms.addAll(body.subTerms());
//        for (int i = 0; i < body.subTerms().size(); i++) {
//            UTerm term1 = body.subTerms().get(i);
//            for (int j = 0; j < body.subTerms().size(); j++) {
//                UTerm term2 = body.subTerms().get(j);
//                if (term1.equals(term2) && i != j) {
//                    subTerms.remove(term2);
//                }
//            }
//        }
//        return USquash.mk(UMul.mk());
//    }
private UTerm simplifyInequalityByCongruence(UTerm expr) {
    expr = transformSubTerms(expr, this::simplifyInequalityByCongruence);
    if (expr.kind() != UKind.MULTIPLY) return expr;

    final UMul multiply = (UMul) expr;

    final NaturalCongruence<UTerm> congruence = NaturalCongruence.mk();
    getEqCongruenceRecursive(multiply, pred -> true, congruence, false);
    expr = replaceInequalityWithZero(multiply, congruence);

    return expr;
}
    public static void getEqCongruenceRecursive(UTerm context,
                                                Function<UPred, Boolean> filter,
                                                NaturalCongruence<UTerm> eqClass,
                                                boolean considerNull) {
        switch (context.kind()) {
            case CONST, STRING, TABLE, FUNC, VAR, ADD, NEGATION -> {
            }
            case PRED -> {
                final UPred pred = (UPred) context;
                if (pred.isPredKind(UPred.PredKind.EQ) && filter.apply(pred)) {
                    final List<UTerm> eqPredTerms = pred.args();
                    assert eqPredTerms.size() == 2;
                    final UTerm termArg0 = eqPredTerms.get(0), termArg1 = eqPredTerms.get(1);
                    eqClass.putCongruent(termArg0, termArg1);
                }
                if (considerNull && isNullPred(pred) && filter.apply(pred)) {
                    final List<UTerm> isNullPredTerms = pred.args();
                    assert isNullPredTerms.size() == 1;
                    final UTerm termArg0 = isNullPredTerms.get(0);
                    eqClass.putCongruent(UConst.nullVal(), termArg0);
                }
            }
            case MULTIPLY, SUMMATION, SQUASH  -> {
                for (final UTerm subTerm : context.subTerms()) {
                    getEqCongruenceRecursive(subTerm, filter, eqClass, considerNull);
                }
            }
            default -> throw new IllegalArgumentException("[Exception] Unsupported U-expression kind: " + context.kind());
        }
    }
    private UTerm replaceInequalityWithZero(UTerm context, NaturalCongruence<UTerm> congruence) {
        if (context instanceof UPred pred
                && (pred.isPredKind(UPred.PredKind.GT)
                || pred.isPredKind(UPred.PredKind.LT))) {
            assert pred.args().size() == 2;
            if (congruence.eqClassOf(pred.args().get(0)).contains(pred.args().get(1))) {
                isModified = true;
                return UConst.zero();
            }
        }

        final List<UTerm> newSubTerms = new ArrayList<>();

        for (final UTerm subTerm : context.subTerms()) {
            newSubTerms.add(replaceInequalityWithZero(subTerm, congruence));
        }

        return remakeTerm(context, newSubTerms);
    }
    ArrayList<UTerm> notNullTerms = new ArrayList<>();
    private UTerm removeIsNullPredOnValue(UTerm expr) {
        expr = transformSubTerms(expr, this::removeIsNullPredOnValue);
        if (expr.kind() != PRED || !isNullPred(expr)) return expr;

        assert ((UPred) expr).args().size() == 1;
        final UTerm predArg = ((UPred) expr).args().get(0);
        if (predArg.kind() != VAR) {
            isModified = true;
            return predArg.equals(UConst.NULL) ? UConst.one() : UConst.zero();
        } else if (notNullTerms.contains(predArg)) {
            isModified = true;
            return UConst.zero();
        }
        return expr;
    }

    private UTerm removeSumEqPred(UTerm expr) {
        expr = transformSubTerms(expr, this::removeSumEqPred);
        if (expr.kind() != PRED) return expr;

        UPred pred = (UPred) expr;
        if (pred.isPredKind(EQ)) {
            UTerm op1 = pred.args().get(0);
            UTerm op2 = pred.args().get(1);
            if (op1.equals(op2))
                return UConst.one();
        }
        return expr;
    }

    public UTerm removeDuplicatePatternPartVar(UTerm expr) {
        expr = transformSubTerms(expr, this::removeDuplicatePatternPartVar);
        if (expr.kind() != MULTIPLY) return expr;
        final NaturalCongruence<UVar> varEqClass = UExprSupport.getEqVarCongruenceInTermsOfMul(expr);
        final UMul mul = (UMul) expr;
        final List<UTerm> subTerms = mul.subTerms();
        final List<UTerm> tables = filter(subTerms, t -> t.kind() == TABLE);
        final List<UTerm> labels = filter(subTerms, t -> t.kind() == TABLE && !((UTable) t).tableName().equals(UName.mk("Node"))
            && !((UTable) t).tableName().equals(UName.mk("Rel")));
        final List<UVar> eqVars = varEqClass.keys().stream().toList();
        for (int i = 0, bound = eqVars.size(); i < bound; ++i) {
            final UVar var0 = eqVars.get(i);
            for (int j = i + 1, bound0 = eqVars.size(); j < bound0; ++j) {
                final UVar var1 = eqVars.get(j);
                if (var0.equals(var1) || !varEqClass.isCongruent(var0, var1)) continue;
                final UVar baseVar0 = var0.args()[0], baseVar1 = var1.args()[0];
                assert baseVar0.is(UVar.VarKind.BASE) && baseVar1.is(UVar.VarKind.BASE);
                final UTerm table0 = linearFind(tables, t -> ((UTable) t).var().equals(baseVar0));
                final UTerm table1 = linearFind(tables, t -> ((UTable) t).var().equals(baseVar1));
                if (table0 == null || table1 == null) continue;
                // Do rewrite here
                mul.subTerms().remove(table1);
                mul.replaceVarInplace(baseVar1, baseVar0, false);
                isModified = true;
            }
        }
        return expr;
    }

    private UTerm removeUnusedSummationBoundedVar(UTerm expr) {
        expr = transformSubTerms(expr, this::removeUnusedSummationBoundedVar);
        if (expr.kind() != SUMMATION) return expr;

        ((USum) expr).removeUnusedBoundedVar();
        return expr;
    }
    public UTerm removeUselessSquashSumFromSumBody(UTerm term) {
        term = transformSubTerms(term, this::removeUselessSquashSumFromSumBody);
        if (term.kind() != SUMMATION) return term;
        USum expr = (USum) term;
        UTerm body = expr.body();
        if (!(body instanceof UMul))
            return expr;
        for (UTerm subTerm : body.subTerms()) {
            if (subTerm instanceof USquash) {
                UTerm squashBody = ((USquash) subTerm).body();
                if (squashBody instanceof USum squashSum) {
                    if (squashSum.boundedVars().size() > expr.boundedVars().size())
                        continue;
                    ArrayList<UTerm> subTerms = new ArrayList<>();
                    subTerms.addAll(body.subTerms());
                    subTerms.remove(subTerm);
                    USum tmp = USum.mk(expr.boundedVars(), UMul.mk(subTerms));
                    if (containSubTerms(tmp, squashSum)) {
                        return tmp;
                    }
                }
            }
        }
        return expr;
    }

    private boolean containSubTerms(USum bigSum, USum smallSum) {
        UTerm bigBody = bigSum.body().copy();
        UTerm smallBody = smallSum.body().copy();
        HashSet<UVar> bigBoundVars = new HashSet<>(bigSum.boundedVars());
        ArrayList<UVar> smallBoundVars = new ArrayList<>(smallSum.boundedVars());

        if (bigBoundVars.size() < smallBoundVars.size()) return false;
        if (bigSum.equals(smallSum)) return true;

        return checkSubSum(0, bigBoundVars, bigBody, smallBoundVars, smallBody);
    }

    boolean checkSubSum(
            int cur, HashSet<UVar> bigBoundVars, UTerm bigBody, ArrayList<UVar> smallBoundVars, UTerm smallBody) {

        if (cur == smallBoundVars.size()) {
            for (UTerm smallTerm : smallBody.subTerms()) {
                if (bigBody.subTerms().contains(smallTerm))
                    continue;
                if (smallTerm.kind() == PRED) {
                    UPred pred = (UPred) smallTerm;
                    if (pred.isTruePred(globalExpr) == 1) continue;
                    if (pred.isPredKind(EQ)) {
                        UTerm op0 = pred.args().get(0);
                        UTerm op1 = pred.args().get(1);
                        NaturalCongruence<UTerm> cong = buildNaturalCongruence(bigBody.subTerms());
                        if (cong.isCongruent(op0, op1)) continue;
                    }
                }
                if (smallTerm.kind() == NEGATION) {
                    if (smallTerm.subTerms().get(0).kind() == PRED) {
                        UPred pred = (UPred) smallTerm.subTerms().get(0);
                        if (isNullPred(pred)) {
                            if (pred.isTruePred(globalExpr) == 0) continue;
                            NaturalCongruence<UTerm> cong = buildNaturalCongruence(bigBody.subTerms());
                            Set<UTerm> eqTerms = cong.eqClassOf(pred.args().get(0));
                            if (any(eqTerms,
                                    t -> bigBody.subTerms().contains(UNeg.mk(mkIsNullPred(t)))))
                                continue;
                        }
                    }
                }
                return false;
            }
            return true;
        }

        final UVar curVar = smallBoundVars.get(cur);
        final UVar newVar = UVar.mkBase(UName.mk(Liastar.newVarName()));
        smallBody = smallBody.replaceVar(curVar, newVar, true);

        for (UVar v : bigBoundVars) {
            final HashSet<UVar> tmpVars = new HashSet<>(bigBoundVars);
            tmpVars.remove(v);
            final UTerm tmpBigBody = bigBody.replaceVar(v, newVar, true);
            final UTerm tmpSmallBody = smallBody.replaceVar(v, newVar, false);
            final boolean result = checkSubSum(cur + 1, tmpVars, tmpBigBody, smallBoundVars, tmpSmallBody);
            if (result) return true;
        }
        return false;
    }
    public static NaturalCongruence<UTerm> buildNaturalCongruence(List<UTerm> terms) {
        NaturalCongruence<UTerm> result = NaturalCongruence.mk();
        buildNaturalCongruenceRecursively(terms, result);
        return result;
    }

    public static void buildNaturalCongruenceRecursively(List<UTerm> terms, NaturalCongruence<UTerm> result) {
        for (UTerm term : terms) {
            switch (term.kind()) {
                case PRED: {
                    UPred pred = (UPred) term;
                    if (!pred.isPredKind(EQ)) continue;
                    result.putCongruent(pred.args().get(0), pred.args().get(1));
                    break;
                }
                case SQUASH: {
                    buildNaturalCongruenceRecursively(((USquash) term).body().subTerms(), result);
                    break;
                }
                case SUMMATION: {
                    buildNaturalCongruenceRecursively(((USum) term).body().subTerms(), result);
                    break;
                }
                case MULTIPLY, ADD: {
                    buildNaturalCongruenceRecursively(term.subTerms(), result);
                    break;
                }
                default: continue;
            }
        }
    }

    public static void getEqCongruenceRecursive(UTerm context,
                                                Function<UPred, Boolean> filter,
                                                NaturalCongruence<UTerm> eqClass,
                                                UTerm fullContext,
                                                boolean considerNull) {
        switch (context.kind()) {
            case CONST, STRING, TABLE, FUNC, VAR -> {
            }
            case PRED -> {
                if (!isCriticalValue(context, fullContext)) return;
                final UPred pred = (UPred) context;
                if (pred.isPredKind(UPred.PredKind.EQ) && filter.apply(pred)) {
                    final List<UTerm> eqPredTerms = pred.args();
                    assert eqPredTerms.size() == 2;
                    final UTerm termArg0 = eqPredTerms.get(0), termArg1 = eqPredTerms.get(1);
                    eqClass.putCongruent(termArg0, termArg1);
                }
                if (considerNull && isNullPred(pred) && filter.apply(pred)) {
                    final List<UTerm> isNullPredTerms = pred.args();
                    assert isNullPredTerms.size() == 1;
                    final UTerm termArg0 = isNullPredTerms.get(0);
                    eqClass.putCongruent(UConst.nullVal(), termArg0);
                }
            }
            case MULTIPLY, SUMMATION, SQUASH, ADD, NEGATION  -> {
                for (final UTerm subTerm : context.subTerms()) {
                    getEqCongruenceRecursive(subTerm, filter, eqClass, fullContext, considerNull);
                }
            }
            default -> throw new IllegalArgumentException("[Exception] Unsupported U-expression kind: " + context.kind());
        }
    }

    public static void getTargetUExprRecursive(UTerm context, Function<UTerm, Boolean> filter, List<UTerm> result, UTerm fullContext) {
        if (filter.apply(context) && isCriticalValue(context, fullContext)) result.add(context);
        switch (context.kind()) {
            case CONST, STRING, TABLE, FUNC, VAR, PRED -> {
            }
            case MULTIPLY, SUMMATION, SQUASH, ADD, NEGATION -> {
                for (final UTerm subTerm : context.subTerms()) {
                    getTargetUExprRecursive(subTerm, filter, result, fullContext);
                }
            }
            default -> throw new IllegalArgumentException("[Exception] Unsupported U-expression kind: " + context.kind());
        }
    }
    public static NaturalCongruence<UTerm> getEqIsNullCongruenceInTermsOfMul(UTerm mulContext, Function<UPred, Boolean> filter) {
        assert mulContext.kind() == UKind.MULTIPLY;
        final NaturalCongruence<UTerm> varEqClass = NaturalCongruence.mk();
        for (UTerm subTerm : mulContext.subTermsOfKind(UKind.PRED)) {
            final UPred pred = (UPred) subTerm;
            if (pred.isPredKind(UPred.PredKind.EQ) && filter.apply(pred)) {
                final List<UTerm> eqPredTerms = pred.args();
                assert eqPredTerms.size() == 2;
                final UTerm termArg0 = eqPredTerms.get(0), termArg1 = eqPredTerms.get(1);
                varEqClass.putCongruent(termArg0, termArg1);
            }
            if (isNullPred(pred) && filter.apply(pred)) {
                final List<UTerm> isNullPredTerms = pred.args();
                assert isNullPredTerms.size() == 1;
                final UTerm termArg0 = isNullPredTerms.get(0);
                varEqClass.putCongruent(UConst.nullVal(), termArg0);
            }
        }
        return varEqClass;
    }
}
