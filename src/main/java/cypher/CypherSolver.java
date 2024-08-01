package cypher;

import cypher.algebra.GraphAlgebraBuilder;
import cypher.algebra.translator.GraphAlgebraTranslator;
import cypher.parser.CypherStringVisitor;
import cypher.translate.Cypher2UExpr;
import cypher.translate.CypherPair;
import cypher.translate.UExprNormalizer;
import representations.GraphAlgebra;
import sqlsolver.logic.SqlSolver;
import sqlsolver.uexpr.UExprSupport;
import sqlsolver.uexpr.UName;
import sqlsolver.uexpr.UTerm;
import sqlsolver.uexpr.UVar;

public class CypherSolver {
    private final CypherPair pair;
    public static long total;
    public CypherSolver(CypherPair pair) {
        this.pair = pair;
    }

    public int solveByAlgebra() {
        CypherStringVisitor visitor1 = new CypherStringVisitor();
        CypherStringVisitor visitor2 = new CypherStringVisitor();
        visitor1.visit(pair.getStmt1());
        visitor2.visit(pair.getStmt2());
        visitor1.print();
        visitor2.print();
        if (visitor1.get().equals(visitor2.get())) {
            return SqlSolver.EQ;
        }
        GraphAlgebraBuilder builder1 = new GraphAlgebraBuilder(pair.getStmt1());
        GraphAlgebraBuilder builder2 = new GraphAlgebraBuilder(pair.getStmt2());
        Cypher2UExpr.OUTER = false;
        Cypher2UExpr.CASE = false;
        GraphAlgebra algebra1 = builder1.build();
        GraphAlgebra algebra2 = builder2.build();
        if (builder1.subQueries.size() != builder2.subQueries.size()) {
            return SqlSolver.NEQ;
        } else {
            for (int i = 0; i < builder1.subQueries.size(); i++) {
                GraphAlgebra a1 = builder1.subQueries.get(i);
                GraphAlgebra a2 = builder2.subQueries.get(i);
                GraphAlgebraTranslator t1 = new GraphAlgebraTranslator(a1);
                GraphAlgebraTranslator t2 = new GraphAlgebraTranslator(a2);
                UTerm expr1 = t1.translate();
                UTerm expr2 = t2.translate();
                int result = solveByLia(expr1, expr2);
                if (result != SqlSolver.EQ) {
                    return SqlSolver.NEQ;
                }else {
                    return SqlSolver.EQ;
                }
            }
        }
        GraphAlgebraTranslator translator1 = new GraphAlgebraTranslator(algebra1);
        Cypher2UExpr.OUTER = false;
        Cypher2UExpr.CASE = false;
        GraphAlgebraTranslator translator2 = new GraphAlgebraTranslator(algebra2);
        UTerm expr1 = translator1.translate();
        UTerm expr2 = translator2.translate();
        int result = solveByLia(expr1, expr2);
        if (result != SqlSolver.EQ) {
            if (translator1.sumBounds.size() == 1 || translator2.sumBounds.size() == 1) {
                GraphAlgebraTranslator.peel = true;
            }
            expr1 = translator1.translate();
            expr2 = translator2.translate();
            result = solveByLia(expr1, expr2);
        }
//        GraphAlgebraTranslator.peel = false;
        return result;
    }
    public int solve() {
        Cypher2UExpr q1 = new Cypher2UExpr(pair.getStmt1(), "x");
        Cypher2UExpr q2 = new Cypher2UExpr(pair.getStmt2(), "x");

        UTerm expr1 = q1.toUExpr();
        UTerm expr2 = q2.toUExpr();

        int result = solveByLia(expr1, expr2);
        return result;
    }

    public int solveByLia(UTerm expr1,UTerm expr2) {
        UExprNormalizer normalizer = new UExprNormalizer();
        long startTime = System.currentTimeMillis();

        expr1 = UExprSupport.normalizeExpr(expr1);
        expr1 = normalizer.normalizeTerm(expr1);
        expr2 = UExprSupport.normalizeExpr(expr2);
        expr2 = normalizer.normalizeTerm(expr2);
        long endTime = System.currentTimeMillis();
        long elapsedTime = endTime - startTime;
        total += elapsedTime;
        System.out.println(expr1);
        System.out.println(expr2);
        SqlSolver sqlSolver = new SqlSolver(expr1, expr2
                , UVar.mkBase(UName.mk("queryTuple")), UVar.mkBase(UName.mk("queryTuple")));
        SqlSolver.initialize();
        int result = sqlSolver.proveEq();
        System.out.println(result == SqlSolver.EQ? "EQ" : "NEQ");
        return result;
    }
}
