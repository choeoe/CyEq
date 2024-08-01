package representations.graphalgebra;

import cypher.ast.expression.Variable;

public class Attr extends ProjOp{
    public Variable var;
    public String attr;

    public Attr(Variable var) {
        this.var = var;
        this.attr = null;
    }

    public Attr(Variable var, String attr) {
        this.var = var;
        this.attr = attr;
    }

    @Override
    public ProjKind kind() {
        return ProjKind.ATTR;
    }
}
