package representations.graphalgebra;

import representations.GraphAlgebra;

import java.util.ArrayList;
import java.util.List;

public class Grouping extends Projection {
    public List<ProjOp> aggs = new ArrayList<>();


    private final String gamma = "\u03B3";
    public Grouping(GraphAlgebra alge) {
        super(alge);
    }

    @Override
    public List<GraphAlgebra> subAlgebras() {
        return relation.subAlgebras();
    }

    @Override
    public Kind kind() {
        return Kind.GROUP;
    }

    @Override
    public String toString() {
        StringBuilder keys = new StringBuilder();
        for (int i = 0; i < this.projs.size(); i++) {
            if (i != 0) {
                keys.append(",");
            }
            keys.append(this.projs.get(i));
        }
        StringBuilder aggs = new StringBuilder();
        for (int i = 0; i < this.aggs.size(); i++) {
            if (i != 0) {
                aggs.append(",");
            }
            aggs.append(this.aggs.get(i));
        }
        return "{%s}%s{%s}(%s)".formatted(keys.toString(),gamma,aggs.toString(),relation.toString());
    }
}
