package representations.graphalgebra;

import cypher.ast.expression.Expression;
import cypher.ast.expression.Property;
import cypher.ast.expression.Variable;

public class Rename extends ProjOp{
    public Expression expr;

    public Variable alias;

    public Rename(Expression expr, Variable alias) {
        this.expr = expr;
        this.alias = alias;
        alias.mkLink(expr);
        if (expr.isPattern()) {
            alias.kind = Variable.VarKind.PATTERN;
        } else if (expr.isProp()) {
            alias.kind = Variable.VarKind.PROJ;
        } else if (expr.isVar()) {
            alias.kind = Variable.VarKind.BASE;
        } else if (expr.isList()) {
            alias.kind = Variable.VarKind.LIST;
        } else {
            alias.kind = Variable.VarKind.EXPR;
        }
    }

    @Override
    public String toString() {
        return expr + "->" + alias;
    }

    @Override
    public ProjKind kind() {
        return ProjKind.RENAME;
    }
}
