package representations.graphalgebra;

import cypher.ast.expression.Expression;

public class ProjExpr extends ProjOp{
    public Expression expr;

    public ProjExpr(Expression expr) {
        this.expr = expr;
    }

    @Override
    public String toString() {
        return expr.toString();
    }

    @Override
    public ProjKind kind() {
        return ProjKind.EXPR;
    }
}
