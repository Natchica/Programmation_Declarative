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

    private void exactlyOne(BoolExpr exprs[]) {
        // at least one constraint
        this.solver.add(this.context.mkOr(exprs));

        // at most one constraint
        for (int i = 0; i < exprs.length; i++) {
            ArrayList<BoolExpr> others = new ArrayList<>();

            for (int j = 0; j < exprs.length; j++) {
                if (j != i) {
                    others.add(this.context.mkNot(exprs[j]));
                }
            }

            this.solver.add(this.context.mkImplies(exprs[i],
                                                   this.context.mkAnd(others.stream().toArray(BoolExpr[]::new))));
        }
    }

    private void addSwapConstraint(int step, int i, int j, boolean useStore) {
        if (useStore) {
            this.solver.add(this.context.mkImplies(
                                this.actions[step][i][j],
                                this.context.mkEq(this.arrays[step + 1],
                                                  this.context.mkStore(
                                                      this.context.mkStore(this.arrays[step],
                                                                           this.context.mkInt(i),
                                                                           this.context.mkSelect(this.arrays[step],
                                                                                                 this.context.mkInt(j))),
                                                      this.context.mkInt(j),
                                                      this.context.mkSelect(this.arrays[step],
                                                                            this.context.mkInt(i))))));
        } else {
            BoolExpr constraints[] = new BoolExpr[this.length];

            for (int k = 0; k < this.length; k++) {
                if (k == i) {
                    constraints[k] =
                        this.context.mkEq(this.context.mkSelect(this.arrays[step + 1],
                                                                this.context.mkInt(i)),
                                          this.context.mkSelect(this.arrays[step],
                                                                this.context.mkInt(j)));
                } else if (k == j) {
                    constraints[k] =
                        this.context.mkEq(this.context.mkSelect(this.arrays[step + 1],
                                                                this.context.mkInt(j)),
                                          this.context.mkSelect(this.arrays[step],
                                                                this.context.mkInt(i)));
                } else {
                    constraints[k] =
                        this.context.mkEq(this.context.mkSelect(this.arrays[step + 1],
                                                                this.context.mkInt(k)),
                                          this.context.mkSelect(this.arrays[step],
                                                                this.context.mkInt(k)));
                }
            }

            this.solver.add(this.context.mkImplies(
                                this.actions[step][i][j],
                                this.context.mkAnd(constraints)));
        }
    }

    private void isSorted(ArrayExpr array, int length) {
        for (int i = 0; i < length - 1; i++) {
            this.solver.add(this.context.mkLe((IntExpr) this.context.mkSelect(array,
                                                                              this.context.mkInt(i)),
                                              (IntExpr) this.context.mkSelect(array,
                                                                              this.context.mkInt(i + 1))));
        }
    }

    public ArraySwaps(int length,
                      int values[]) {
        // init Z3 solver
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");
        cfg.put("proof", "true");

        this.context = new Context(cfg);
        this.solver  = context.mkSolver();

        // init Z3 arrays
        this.length = length;
        this.values = values;
        this.arrays = new ArrayExpr[4];

        for (int i = 0; i < 4; i++) {
            this.arrays[i] = context.mkArrayConst("array_step_" + i,
                                                  context.getIntSort(),
                                                  context.getIntSort());
        }

        // add constraints to represent initial state
        for (int i = 0; i < this.length; i++) {
            this.solver.add(this.context.mkEq(
                                this.context.mkSelect(this.arrays[0],
                                                      this.context.mkInt(i)),
                                this.context.mkInt(values[i])));
        }

        // init actions
        this.actions = new BoolExpr[3][this.length][this.length];

        for (int s = 0; s < 3; s++) {
            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    this.actions[s][i][j] =
                        this.context.mkBoolConst("" + s + "_swap_" + i + "_" + j);
                }
            }
        }

        // actions "effects"
        for (int s = 0; s < 3; s++) {
            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    this.addSwapConstraint(s, i, j, useStore);
                }
            }
        }

        // exactly one action at each step
        for (int s = 0; s < 3; s++) {
            // build array
            BoolExpr[] exprs = new BoolExpr[this.length * this.length];

            for (int i = 0; i < this.length; i++) {
                for (int j = 0; j < this.length; j++) {
                    exprs[i * this.length + j] = this.actions[s][i][j];
                }
            }

            this.exactlyOne(exprs);
        }

        // the last array is sorted
        this.isSorted(this.arrays[3], this.length);
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
