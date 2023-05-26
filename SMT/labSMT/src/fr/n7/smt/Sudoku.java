// package fr.n7.smt;

// import java.io.*;
// import java.util.*;
// import com.microsoft.z3.*;

// class OutOfBoundsException extends Exception {
//     public OutOfBoundsException(String message) {
//         super(message);
//     }
// }

// class Sudoku {
//     // Sudoku dimension
//     private int                 nInit;
//     private Context             context;
//     private Solver              solver;

//     // a cube representing the grid
//     private IntExpr grid[][];

//     // the initial values on the grid represented as
//     // boolean values
//     private ArrayList<IntExpr>  initValues;

//     /**
//      * This method should add existence constraints: each cell has
//      * at least one value.
//      */
//     private void addExistenceConstraints() {
//         for (int i = 0; i < this.grid.length; i++) {
//             for (int j = 0; j < this.grid.length ; j++) {
//                 this.solver.add(this.context.mkGe(this.grid[i][j],context.mkInt(1)));
//                 this.solver.add(this.context.mkLe(this.grid[i][j],context.mkInt(9)));
//             }
//         }
//     }

//     /**
//      * This method should add columns constraints: each value
//      * appears exactly one time in each column.
//      */
//     private void addColumnConstraints() {
//         for (int j = 0; j < this.grid.length; j++) {
//             for (int k = 0; k < this.grid.length; k++) {
//                 // each value k should happen in each column j
//                 BitVecSort bvSort = context.mkBitVecSort(9);

//                 ArrayExpr set = context.mkArrayConst("set",
//                                                     context.getIntSort(),
//                                                     bvSort);

//                 for (int i = 0; i < this.grid.length ; i++) {
//                     set.add(this.grid[i][j] );
//                 }

//                 this.solver.add(this.context.mkOr(set.toArray(new BoolExpr[0])));

//                 // each value k appears at most one time in each
//                 // column
//                 for (int i1 = 0; i1 < this.grid.length; i1++) {
//                     for (int i2 = 0; i2 < this.grid.length; i2++) {
//                         if (i1 != i2) {
//                             this.solver.add(this.context.mkImplies(
//                                                 this.grid[i1][j][k],
//                                                 this.context.mkNot(this.grid[i2][j][k])
//                                                 ));
//                         }
//                     }
//                 }
//             }
//         }
//     }

//     /**
//      * This method should add rows constraints: each value
//      * appears exactly one time in each row.
//      */
//     private void addRowConstraints() {
//       // TODO : to be implemented!
//     }

//     /**
//      * This method should add subgrids constaints: each value
//      * appears exactly one time in each subgrid.
//      */
//     private void addSubGridsConstraints() {
//       // TODO : to be implemented!
//     }

//     /**
//      * Build a Sudoku problem.
//      *
//      * @param n the Sudoku dimension. The row and column length
//      *          is therefore n * n.
//      */
//     Sudoku(int n) {
//         this.initValues = new ArrayList<>();

//         HashMap<String, String> cfg = new HashMap<String, String>();
//         cfg.put("model", "true");

//         this.context = new Context(cfg);
//         this.solver  = context.mkSolver();
//         this.nInit   = n;

//         int w = n * n;

//         // TODO: find the right type!
//         this.grid = new IntExpr[w][w];

//         // build Z3 decision variables for each cell/value
//         for (int i = 0; i < w; i++) {
//             for (int j = 0; j < w; j++) {
//                 for (int k = 0; k < w; k++) {
//                     // TODO: properly initialize grid!
//                     this.grid[i][j] = null;
//                 }
//             }
//         }

//         long startTime = System.currentTimeMillis();

//         this.addExistenceConstraints();
//         this.addColumnConstraints();
//         this.addRowConstraints();
//         this.addSubGridsConstraints();

//         long stopTime    = System.currentTimeMillis();
//         long elapsedTime = stopTime - startTime;

//         System.out.println("time to build constraints: " + elapsedTime + "ms");
//     }

//     /**
//      * Prints Sudoku solution if it exists.
//      */
//     void print() {
//         Model m = this.solver.getModel();

//         if (m == null) {
//             return;
//         }

//         for (int i = 0; i < this.grid.length; i++) {
//             for (int j = 0; j < this.grid.length; j++) {
//                 // TODO: print value

//             }

//             System.out.println();
//         }
//     }

//     /**
//      * Solves the current Sudoku problem.
//      */
//     Status solve() {
//         long startTime = System.currentTimeMillis();

//         Status s = this.solver.check();

//         long stopTime    = System.currentTimeMillis();
//         long elapsedTime = stopTime - startTime;

//         System.out.println("time to solve problem: " + elapsedTime + "ms");

//         return s;
//     }

//     /**
//      * Adds a value in the grid as initial constraint.
//      *
//      * @param i the row of the value
//      * @param j the column of the value
//      * @param v the value
//      */
//     void addValue(int i, int j, int v) throws OutOfBoundsException {
//         if (i < 0 || j < 0 || v < 1 ||
//             i >= this.grid.length || j >= this.grid.length || v > this.grid.length) {
//             throw new OutOfBoundsException(String.format("problem when adding (%d, %d, %d)", i , j, v));
//         }

//         this.initValues.add(this.grid[i][j]);
//         // TODO: find constraint to add!
//     }

//     /**
//      * Loads an initial situation from a file and returns the
//      * corresponding Sudoku.
//      *
//      * @param filename a CSV file containing the initial situation
//      * @return a Sudoku object
//      */
//     static Sudoku loadSudoku(String filename) throws OutOfBoundsException, IOException {
//         BufferedReader br = new BufferedReader(new FileReader(filename));

//         // first line contains dimension
//         String line   = br.readLine();
//         int    n      = Integer.parseInt(line);
//         Sudoku sudoku = new Sudoku(n);

//         // parse each line
//         int i = 0;

//         while ((line = br.readLine()) != null) {
//             String values[] = line.split(",");

//             for (int j = 0; j < values.length; j++) {
//                 if (! values[j].equals("")) {
//                     sudoku.addValue(i, j, Integer.parseInt(values[j]));
//                 }
//             }

//             i++;
//         }

//         return sudoku;
//     }

//     /**
//      * A simple program to load a Sudoku from a file using
//      * command line arguments.
//      *
//      * If you use the Makefile, use the following command:
//      *
//      * make run-sudoku SUDOKU_FILE=file_to_use
//      */
//     public static void main(String[] args) throws OutOfBoundsException, IOException {
//         Sudoku            sudoku = Sudoku.loadSudoku(args[0]);
//         InputStreamReader aux    = new InputStreamReader(System.in);
//         BufferedReader    in     = new BufferedReader(aux);

//         if (sudoku.solve() == Status.SATISFIABLE) {
//             System.out.println("Solution found!\n");

//             sudoku.print();
//         } else {
//             System.out.println("No solution found!\n");
//         }
//     }
// }
