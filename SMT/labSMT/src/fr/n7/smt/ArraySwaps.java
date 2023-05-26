package fr.n7.smt;

import java.util.*;
import com.microsoft.z3.*;

public class ArraySwaps {

    private Context        context;
    private Solver         solver;
    private int            length;
    private int[]          values;
    private ArrayExpr[]    arrays;
    private BoolExpr[][][] actions;
    private static boolean useStore = true;

    public ArraySwaps(int length,
                      int values[]) {
        // init Z3 solver
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        cfg.put("proof", "true");

        this.context = new Context(cfg);
        this.solver  = context.mkSolver();

    }

    private String arrayToString(ArrayExpr array, Model m, int length) {
        StringBuilder sb = new StringBuilder("");

        sb.append("[ ");

        for (int i = 0; i < length; i++) {
            sb.append(m.eval(this.context.mkSelect(array,
                                                   this.context.mkInt(i)),
                             true) +
                      (i != length - 1 ? ", " : ""));
        }

        sb.append(" ]");

        return sb.toString();
    }

    private String decisionToString(int step, Model m) {
        String decision = null;

        for (int i = 0; i < this.length; i++) {
            for (int j = 0; j < this.length; j++) {
                if (m.getConstInterp(actions[step][i][j]).isTrue()) {
                    if (decision == null) {
                        decision = actions[step][i][j].toString();
                    } else {
                        System.err.println("*** Problem: at least two decisions for the same step! ***");
                        System.err.println("   " + decision.toString() + " and " +
                                           actions[step][i][j].toString());
                        System.exit(1);
                    }
                }
            }
        }

        return decision;
    }

    public void solveAndPrint() {
        System.out.print("* User input: [");

        for (int i = 0; i < this.length; i++) {
            System.out.print(" " + this.values[i] + (i != (this.length - 1) ? "," : ""));
        }

        System.out.println(" ]");

        System.out.println("* Solving problem");

        this.arrays = new ArrayExpr[4];
        this.actions = new BoolExpr[3][this.length][this.length];

        // create the arrays
        for (int s = 0; s < 4; s++) {
            this.arrays[s] = this.context.mkArrayConst("array" + s,
                                                       this.context.getIntSort(),
                                                       this.context.getIntSort());
        }

        // create the actions
        for (int s = 0; s < 3; s++) {
            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    this.actions[s][i][j] = this.context.mkBoolConst("action" + s + "_" + i + "_" + j);
                }
            }
        }

        // add the constraints
        // 1. initial state
        for (int i = 0; i < this.length; i++) {
            this.solver.add(this.context.mkEq(this.context.mkSelect(this.arrays[0],
                                                                    this.context.mkInt(i)),
                                              this.context.mkInt(this.values[i])));
        }

        // 2. 1 action chosen per step
        for (int s = 0; s < 3; s++) {
            BoolExpr[] ors = new BoolExpr[this.length * this.length];

            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    ors[i * this.length + j] = this.actions[s][i][j];
                }this.solver.add(this.context.mkEq(this.context.mkSelect(this.arrays[0],
                this.context.mkInt(i)),
this.context.mkInt(this.values[i])));
            }

            this.solver.add(this.context.mkOr(ors));
        }

        // 3. tab[step][i][j] = tab[step + 1][j][i]
        for (int s = 0; s < 3; s++) {
            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    this.solver.add(this.context.mkAnd(
                        this.context.mkEq(this.context.mkSelect(this.arrays[s + 1], this.context.mkInt(i)),
                                          this.context.mkSelect(this.arrays[s],     this.context.mkInt(j))),
                        this.context.mkEq(this.context.mkSelect(this.arrays[s + 1], this.context.mkInt(j)),
                                          this.context.mkSelect(this.arrays[s],     this.context.mkInt(i)))
                                                      )
                                    );
                }
            }
        }

        // 4. tab is sorted
        for (int i = 0; i < this.length - 1; i++) {
            this.solver.add(this.context.mkLe((ArithExpr) this.context.mkSelect(this.arrays[3],
                                                                    this.context.mkInt(i)),
                                              (ArithExpr) this.context.mkSelect(this.arrays[3],
                                                                    this.context.mkInt(i + 1))));

        }


        if (this.solver.check() == Status.SATISFIABLE) {
            System.out.println("  Problem is SAT!");

            Model m = this.solver.getModel();

            for (int s = 0; s < 4; s++) {
                System.out.println("  " + s + ". array: " +
                                   this.arrayToString(this.arrays[s], m, this.length));
                if (s != 3) {
                    System.out.println("     decision: " + this.decisionToString(s, m));
                }
            }
        } else {
            System.out.println("  UNSAT or UNKNOWN problem!");
        }
    }
}
