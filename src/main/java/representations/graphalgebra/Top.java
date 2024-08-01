package representations.graphalgebra;

import cypher.ast.clause.projection.Limit;
import cypher.ast.expression.Expression;
import representations.GraphAlgebra;

import java.util.ArrayList;
import java.util.List;

public class Top implements GraphAlgebra {
    public GraphAlgebra algebra;
    public Limit limit;

    private final String lambda = "\u03BB";
    public Top(Limit limit, GraphAlgebra algebra) {
        this.algebra = algebra;
        this.limit = limit;
    }

    @Override
    public List<GraphAlgebra> subAlgebras() {
        return new ArrayList<>(algebra.subAlgebras());
    }

    @Override
    public Kind kind() {
        return Kind.TOP;
    }

    @Override
    public String toString() {
        return "%s{%s}(%s)".formatted(lambda, limit, algebra);
    }
}
