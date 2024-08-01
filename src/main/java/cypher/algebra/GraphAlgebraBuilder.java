package cypher.algebra;

import cypher.ast.QueryPart;
import cypher.ast.SingleQuery;
import cypher.ast.Statement;
import cypher.ast.Union;
import cypher.ast.clause.Clause;
import cypher.ast.clause.Unwind;
import cypher.ast.clause.Where;
import cypher.ast.clause.match.Match;
import cypher.ast.clause.match.pattern.*;
import cypher.ast.clause.projection.*;
import cypher.ast.expression.*;
import cypher.parser.CypherStringVisitor;
import cypher.translate.CypherNormalizer;
import org.apache.commons.lang3.tuple.Pair;
import representations.GraphAlgebra;
import representations.graphalgebra.*;

import java.util.ArrayList;
import java.util.List;

public class GraphAlgebraBuilder {
    public Statement stmt;

    public GraphAlgebra graphAlgebra;
    public List<GraphAlgebra> subQueries = new ArrayList<>();
    public GraphAlgebraBuilder(Statement stmt) {
        this.stmt = stmt;
    }

    private GraphAlgebra lastOrderWithLIMIT = null;
    public GraphAlgebra build() {
        CypherStringVisitor visitor = new CypherStringVisitor();
        visitor.visit(stmt);
        CypherNormalizer.normalize(stmt, "x");
        graphAlgebra = buildQueryPart(stmt.query.part);
        System.out.println(graphAlgebra);
        return graphAlgebra;
    }

    public GraphAlgebra buildQueryPart(QueryPart part) {
        if (part instanceof SingleQuery singleQuery) {
            return buildSingle(singleQuery);
        } else if (part instanceof Union.Distinct union) {
            return new representations.graphalgebra.Union(buildQueryPart(union.lhs),
                    buildQueryPart(union.rhs));
        } else {
            Union.All all = ((Union.All) part);
            return new BUnion(buildQueryPart(all.lhs), buildQueryPart(all.rhs));
        }
    }

    private GraphAlgebra buildSingle(SingleQuery singleQuery) {
        GraphAlgebra algebra = null;
        for (Clause clause : singleQuery.clauses) {
            if (clause instanceof Match match) {
                GraphAlgebra pattern = buildPatternParts(match.pattern.patternParts);
                if (algebra == null) {
                    algebra = pattern;
                    if (match.optional)
                        algebra = new LOJoin(new EmptySet(), algebra);
                    if (match.where.isPresent()) {
                        algebra = wrapSelection(algebra, match.where.get());
                    }
                } else {
                    if (match.optional)
                        algebra = new LOJoin(algebra, pattern);
                    algebra = new Join(algebra, pattern);
                }
            }
            if (clause instanceof Unwind unwind) {
                algebra = buildUnwind(algebra, unwind);
            }
            if (clause instanceof ProjectionClause proj) {
                algebra = buildProj(algebra, proj);
            }
        }
        return algebra;
    }

    private GraphAlgebra buildUnwind(GraphAlgebra algebra, Unwind unwind) {
        Expression expr = unwind.expr;
        Variable alias = unwind.alias;
        return new UnwindAlge(algebra, expr, alias);
    }

    private boolean containsAgg(ProjectionClause proj) {
        List<ReturnItem> returnItems = proj.returnItems;
        for (ReturnItem item : returnItems) {
            item.expression.isAggExpression();
            return true;
        }
        return false;
    }

    private GraphAlgebra buildProj(GraphAlgebra alge, ProjectionClause proj) {
//        if (containsAgg(proj)) {
//            return buildGrouping(alge, proj);
//        }
        GraphAlgebra algebra;
        Projection projection = new Projection(alge);
        if (proj instanceof Return) {
            projection.outer();
        }
        for (ReturnItem returnItem : proj.returnItems) {
            Expression expr = returnItem.expression;
            if (returnItem instanceof ReturnItem.Unaliased) {
                projection.projs.add(new ProjExpr(expr));
            } else {
                assert returnItem instanceof ReturnItem.Aliased;
                Variable var = ((ReturnItem.Aliased) returnItem).alias;
                projection.projs.add(new Rename(expr, var));
            }
        }
        if (proj.distinct) {
            algebra = new Dedup(projection);
        } else
            algebra = projection;
        if (proj.orderBy.isPresent()) {
            OrderBy orderBy = proj.orderBy.get();
            Sort sort = new Sort(algebra);
            if (proj instanceof Return) {
                sort.outer();
            }
            sort.sortItems = orderBy.sortItems;
            algebra = sort;
        }
        if (proj.limit.isPresent()) {
            if (projection.isOuter()) {
                Limit limit = proj.limit.get();
                algebra = new Top(limit, algebra);
            } else {
                Limit limit = proj.limit.get();
                Projection clone = projection.copy();
                clone.outer();
                subQueries.add(new Top(limit, clone));
            }
        }
        if (proj instanceof With with) {
            if (with.where.isPresent()) {
                algebra = wrapSelection(algebra, with.where.get());
            }
        }
        return algebra;
    }

    private GraphAlgebra buildGrouping(GraphAlgebra alge, ProjectionClause proj) {
        GraphAlgebra algebra;
        Grouping grouping = new Grouping(alge);
        if (proj instanceof Return) {
            grouping.outer();
        }
        for (ReturnItem returnItem : proj.returnItems) {
            Expression expr = returnItem.expression;
            if (returnItem instanceof ReturnItem.Unaliased) {
                if(returnItem.expression.isAggExpression())
                    grouping.aggs.add(new ProjExpr(expr));
                else
                    grouping.projs.add(new ProjExpr(expr));
            } else {
                assert returnItem instanceof ReturnItem.Aliased;
                Variable var = ((ReturnItem.Aliased) returnItem).alias;
                if(returnItem.expression.isAggExpression())
                    grouping.aggs.add(new Rename(expr, var));
                else
                    grouping.projs.add(new Rename(expr, var));
            }
        }
        if (proj.distinct) {
            algebra = new Dedup(grouping);
        } else
            algebra = grouping;
        if (proj.orderBy.isPresent()) {
            OrderBy orderBy = proj.orderBy.get();
            Sort sort = new Sort(algebra);
            if (proj instanceof Return) {
                sort.outer();
            }
            sort.sortItems = orderBy.sortItems;
            algebra = sort;
        }
        if (proj.limit.isPresent()) {
            Limit limit = proj.limit.get();
            algebra = new Top(limit, algebra);
        }
        if (proj instanceof With with) {
            if (with.where.isPresent()) {
                algebra = wrapSelection(algebra, with.where.get());
            }
        }
        return algebra;
    }

    public GraphAlgebra wrapSelection(GraphAlgebra algebra, Where where) {
        return new Selection(algebra, where.expression);
    }

    private GraphAlgebra buildPatternParts(List<PatternPart> patternParts) {
        List<GraphAlgebra> algebras = new ArrayList<>();
        for (PatternPart patternPart : patternParts) {
            GraphAlgebra ele = buildPatternElement(patternPart.element);
            algebras.add(ele);
        }
        if (algebras.size() > 1) {
            return algebras.stream().reduce(Join::new).get();
        } else
            return algebras.get(0);
    }

    private GraphAlgebra buildPatternElement(PatternElement element) {
        if (element instanceof NodePattern node) {
            return buildNode(node);
        } else {
            RelationshipChain chain = ((RelationshipChain) element);
            return buildRelChain(chain);
        }
    }

    private Node buildNode(NodePattern node) {
        assert node.variable.isPresent();
        Variable var = node.variable.get();
        Node nodeAlgebra = new Node(var);
        if (node.properties.isPresent()) {
            MapExpression map = node.properties.get();
            nodeAlgebra.constraint = buildExprFromMapExpr(var, map);
        }
        if (!node.labels.isEmpty()) {
            for (LabelName label : node.labels) {
                nodeAlgebra.labels.add(label.name);
            }
        }
        return nodeAlgebra;
    }

    private Expression buildExprFromMapExpr(Variable var, MapExpression mapExpression) {
        List<Pair<PropertyKeyName, Expression>> props = mapExpression.props;
        List<Expression> exprs = new ArrayList<>();
        for (Pair<PropertyKeyName, Expression> prop : props) {
            Property property = new Property(var, prop.getLeft());
            exprs.add(new Binary.Equals(property, prop.getRight()));
        }
        if (exprs.size() > 1)
            return exprs.stream().reduce(Binary.And::new).get();
        else return exprs.get(0);
    }

    private GraphAlgebra buildRelChain(RelationshipChain chain) {
        assert chain.relationship.variable.isPresent();
        GraphAlgebra algebra = buildNode(chain.rightNode);
        while (true) {
            Variable var = chain.relationship.variable.get();
            PatternElement element = chain.element;
            NodePattern node;
            if(element instanceof RelationshipChain)
                node = ((RelationshipChain) element).rightNode;
            else
                node = ((NodePattern) element);
            Expand expand = new Expand(var, buildNode(node), buildNode(chain.rightNode), algebra);
            if (chain.relationship.direction == RelationshipPattern.SemanticDirection.OUTGOING) {
                expand.setDirection(Expand.Direction.OUT);
            } else if (chain.relationship.direction == RelationshipPattern.SemanticDirection.INCOMING)
                expand.setDirection(Expand.Direction.IN);
            else
                expand.setDirection(Expand.Direction.BOTH);
            if (chain.relationship.properties.isPresent()) {
                MapExpression map = chain.relationship.properties.get();
                expand.constraint = buildExprFromMapExpr(var, map);
            }
            if (!chain.relationship.types.isEmpty()) {
                for (RelTypeName type : chain.relationship.types) {
                    expand.labels.add(type.name);
                }
            }
            algebra = expand;
            if(element instanceof RelationshipChain chain1)
                chain = chain1;
            else
                break;
        }
        return algebra;
    }
}
