package cypher.ast.expression;

import org.apache.commons.lang3.tuple.ImmutablePair;
import org.apache.commons.lang3.tuple.Pair;

import java.util.ArrayList;
import java.util.List;

/**
 */
public class MapExpression extends Expression {

    public List<Pair<PropertyKeyName, Expression>> props;

    public Variable variable;

    public MapExpression(final List<Pair<PropertyKeyName, Expression>> props) {
        this.props = props;
    }

    @Override
    public String toString() {
        StringBuilder prs = new StringBuilder();
        for (int i = 0; i < props.size(); i++) {
            prs.append(props.get(i).getLeft().name).append(":").append(props.get(i).getRight());
            if (i != props.size() - 1) {
                prs.append(",");
            }
        }
        return "{"+prs+"}";
    }

    @Override
    public MapExpression copy() {
        List<ImmutablePair<PropertyKeyName, Expression>> clone = props.stream().map(x -> new ImmutablePair<>(x.getLeft(), x.getRight().copy())).toList();
        List<Pair<PropertyKeyName, Expression>> props = new ArrayList<>(clone);
        return new MapExpression(props);
    }
}
