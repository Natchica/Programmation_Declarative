package fr.n7.sat;

import java.io.*;
import com.microsoft.z3.*;

class Sudoku {

    private static final Logger LOGGER = Logger.getLogger(fr.n7.sat.Sudoku.class.getName());
    private static final ConsoleHandler CONSOLE_HANDLER = new ConsoleHandler();

    private int nInit;
    // Context used to build Z3 Expr encoding the Sudoku Problem
    private Context context;
    // Z3 Solver which build constraints arre added and used to solve the Sudoku Problem
    private Solver  solver;
    // an attribute containing the decision variable
    private BoolExpr[][][] grid;
    // an attribute containing the values provided by the user as decision variables
    private BoolExpr[][][] initValues;
    // Control of the verbose mode
    private boolean logEnabled;

    // Game Rules
    // 1. The grid must be n² x n²
    // 2. Each cell can contain a value in {1, ..., n²}
    // 3. Each cell must contain a value
    // 4. Each row must contain each value exactly once
    // 5. Each column must contain each value exactly once
    // 6. Each block must contain each value exactly once

    // Constructor
    public Sudoku(int n, boolean logEnabled) {
    
        this.logEnabled = logEnabled;

        if(this.logEnabled) {
            CONSOLE_HANDLER.setLevel(Level.FINE);
            LOGGER.setLevel(Level.FINE);
            LOGGER.info("FINE Log initialized");
        } else {
            CONSOLE_HANDLER.setLevel(Level.INFO);
            LOGGER.setLevel(Level.INFO);
            LOGGER.info("INFO Log initialized");
        }

        // initialize initial values
        this.nInit      = n;
        this.grid       = new BoolExpr[n][n][n];
        this.initValues = new BoolExpr[n][n][n];

        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("model", "true");

        this.context    = new Context(cfg);
        this.solver     = context.mkSolver();  

    }

    static Sudoku loadSudoku(String filename, boolean logEnabled) throws IOException {
        BufferedReader br = new BufferedReader(new FileReader(filename));

        // first line contains dimension
        String line   = br.readLine();
        int    n      = Integer.parseInt(line);
        Sudoku sudoku = new Sudoku(); // you should use YOUR
                                      // constructor here!

        // parse each line
        int i = 0;

        while ((line = br.readLine()) != null) {
            String values[] = line.split(",");

            for (int j = 0; j < values.length; j++) {
                if (! values[j].equals("")) {
                    System.out.println("found value " + values[j] +
                                       " at position (" + i + ", " + j + ")");
                    // you should add the value in your Sudoku here!
                }
            }

            i++;
        }

        br.close();

        return sudoku;
    }

}
