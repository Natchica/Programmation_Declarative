JAVAC = javac
JAVA = java
PATH_TO_Z3 = /mnt/nosave/cgarion/z3/bin
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
_LOG = $(if $(LOG), -Dfr.n7.sat.log=true,)
JAVA_OPTS = $(CP_OPTS):./classes $(_LOG) -Djava.library.path=$(PATH_TO_Z3)
SRC_DIR = src/fr/n7/sat
FILE = ./files/easy.csv

_SRC_FILES = Sudoku.java SudokuFirstExampleMain.java SudokuInteractiveMain.java SudokuFromFileMain.java SimpleBooleanProblem.java
SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

.PHONY: compile run-example run-sudoku-first-example run-sudoku-interactive run-sudoku-loader clean

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

run-example: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SimpleBooleanProblem

run-sudoku-first-example: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SudokuFirstExampleMain

run-sudoku-interactive: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SudokuInteractiveMain

run-sudoku-loader: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SudokuFromFileMain $(FILE)

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~
