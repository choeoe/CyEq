package cypher.ast.expression;


public class ExistsFunction extends Expression {

    public Expression arg;

    public ExistsFunction(Expression arg) {
        this.arg = arg;
    }

    @Override
    public String toString() {
        return "EXISTS ( " + arg.toString()+" ) ";
    }

    @Override
    public Expression copy() {
        return new ExistsFunction(arg.copy());
    }
}
