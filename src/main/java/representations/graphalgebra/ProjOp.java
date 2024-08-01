package representations.graphalgebra;

public abstract class ProjOp {
    public enum ProjKind {
        EXPR,
        ATTR,
        RENAME
    }

    public abstract ProjKind kind();
}
