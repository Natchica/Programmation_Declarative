JAVAC = javac
JAVA = java
PATH_TO_Z3 = /mnt/nosave/cgarion/z3/bin
CP_OPTS = -cp $$CLASSPATH:$(PATH_TO_Z3)/com.microsoft.z3.jar
JAVAC_OPTS = $(CP_OPTS) -d classes
JAVA_OPTS = $(CP_OPTS):./classes -Djava.library.path=$(PATH_TO_Z3)
SRC_DIR = src/fr/n7/sat

_SRC_FILES = SimpleBooleanProblem.java
SRC_FILES = $(patsubst %,$(SRC_DIR)/%,$(_SRC_FILES))

.PHONY: compile run-example

compile: $(SRC_FILES) | classes
	$(JAVAC) $(JAVAC_OPTS) $^

export LD_LIBRARY_PATH=/mnt/nosave/cgarion/z3/bin

run-example: compile
	$(JAVA) $(JAVA_OPTS) fr.n7.sat.SimpleBooleanProblem

classes:
	mkdir -p $@

clean:
	- rm -rf classes *.log **/*~
