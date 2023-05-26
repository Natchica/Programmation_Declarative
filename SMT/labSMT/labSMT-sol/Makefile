JAVAC = javac
JAVA = java
PATH_TO_Z3 = /mnt/n7fs/ens/tp_dupont/z3/bin
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
JAVA_OPTS = $(CP_OPTS):./classes -Djava.library.path=$(PATH_TO_Z3)
SRC_DIR = src/fr/n7/smt

_SRC_FILES = SimpleIntegerProblem.java SimpleBVProblem.java CheckingOverflowBV.java \
	SimpleArrayProblem.java Sudoku.java SudokuFirstExampleMain.java \
	SudokuInteractiveMain.java SudokuFromFileMain.java \
	ArraySwaps.java MainArrayCLI.java

SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

.PHONY: compile run-example

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

run-example-int: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SimpleIntegerProblem

run-example-bv: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SimpleBVProblem

run-example-overflow: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.CheckingOverflowBV

run-example-array: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SimpleArrayProblem

run-first-example: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SudokuFirstExampleMain

run-interactive: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SudokuInteractiveMain

run-loader: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.SudokuFromFileMain $(FILE)

run-array-swaps: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.smt.MainArrayCLI

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~
