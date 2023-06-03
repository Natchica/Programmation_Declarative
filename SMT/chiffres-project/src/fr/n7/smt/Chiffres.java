/* Groupe L2
 * GAUD Nathan
 * AMOROS Louis
 */

package fr.n7.smt;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;

import com.microsoft.z3.*;

/**
 * Classe qui implémente l'algorithme de BMC pour la partie "chiffres"
 * du jeu "des chiffres et des lettres".
 */
public class Chiffres {

    /**
     * Contexte utilisé par l'instance Chiffres pour créer les formules,
     * solveurs, etc.
     */
    private Context context;

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, BoolExpr> boolCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, BitVecExpr> bvCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, IntExpr> intCache = new HashMap<>();

    /** Cache de constantes booléennes, indicé par leur nom. */
    private HashMap<String, ArrayExpr> arrayCache = new HashMap<>();

    /** Nombre de bits de la représentation des bitvectors. */
    private int bvBits;

    /** Sorte bitvector de taille bvBits. */
    private Sort bvSort;

    /**
     * Sorte tableaux à indices intSort et elements bitvectors de
     * taille bvBits.
     */
    private Sort bvArraySort;

    /** Sorte des entiers mathématiques. */
    private Sort intSort;

    /** Constantes numériques pour le calcul du système de transition. */
    private int[] nums;

    /** Valeur cible du calcul du système de transition. */
    private int target;

    /** Nombre maximum d'étapes de calcul du système de transition. */
    private int maxNofSteps;

    /** Si vrai alors interdiction d'overflow sur les operations bitvector. */
    private boolean noOverflows;
    private BigInteger maxBvRange;
    private BigInteger minBvRange;

    /**
     * Initialise tous les attributs de la classe: paramètres utilisateur,
     * contexte, sortes.
     */
    public Chiffres(int[] _nums, int _target, int _bvBits, boolean _noOverflows) {
        nums = _nums;
        target = _target;
        bvBits = _bvBits;
        maxBvRange = new BigInteger("2").pow(bvBits - 1).subtract(new BigInteger("1"));
        minBvRange = new BigInteger("2").pow(bvBits - 1).negate();
        maxNofSteps = 2 * nums.length - 1;
        noOverflows = _noOverflows;

        HashMap<String, String> cfg = new HashMap<>();
        cfg.put("model", "true");
        cfg.put("proof", "true");

        context = new Context(cfg);
        intSort = context.mkIntSort();
        bvSort = context.mkBitVecSort(bvBits);
        bvArraySort = context.mkArraySort(intSort, bvSort);
        boolCache = new HashMap<>();
        bvCache = new HashMap<>();
        intCache = new HashMap<>();
        arrayCache = new HashMap<>();
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BoolExpr boolConst(String name) {
        BoolExpr res = boolCache.get(name);

        if (res == null) {
            res = context.mkBoolConst(name);
            boolCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private BitVecExpr bvConst(String name) {
        BitVecExpr res = bvCache.get(name);

        if (res == null) {
            res = context.mkBVConst(name, bvBits);
            bvCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private IntExpr intConst(String name) {
        IntExpr res = intCache.get(name);

        if (res == null) {
            res = context.mkIntConst(name);
            intCache.put(name, res);
        }

        return res;
    }

    /**
     * Retourne la constante du cache si présente, ou bien en crée une
     * nouvelle avec le nom donné si absente.
     */
    private ArrayExpr arrayConst(String name) {
        ArrayExpr res = arrayCache.get(name);

        if (res == null) {
            res = context.mkArrayConst(name, intSort, bvSort);
            arrayCache.put(name, res);
        }

        return res;
    }

    /** Expression vraie ssi exactement une des exprs est vraie. */
    private BoolExpr exactlyOne(BoolExpr... exprs) {
        return context.mkAnd(context.mkOr(exprs), atMostOne(exprs));
    }

    /** Expression vraie ssi au plus une des exprs est vraie. */
    private BoolExpr atMostOne(BoolExpr... exprs) {
        ArrayList<BoolExpr> conjuncts = new ArrayList<>();

        for (BoolExpr expr : exprs) {
            ArrayList<BoolExpr> otherExprs = new ArrayList<>();
            for (BoolExpr e : exprs) {
                if (e != expr) {
                    otherExprs.add(e);
                }
            }

            BoolExpr bigOr = context.mkOr(otherExprs.stream().toArray(BoolExpr[]::new));
            BoolExpr res = context.mkImplies(expr, context.mkNot(bigOr));

            conjuncts.add(res);
        }

        return context.mkAnd(conjuncts.stream().toArray(BoolExpr[]::new));
    }

    /** Convertit un int java en valeur symbolique bitvector Z3. */
    private BitVecNum toBvNum(int num) {
        if (noOverflows) {
            BigInteger bigNum = new BigInteger(String.valueOf(num));

            if (bigNum.compareTo(minBvRange) >= 0 && bigNum.compareTo(maxBvRange) <= 0)
                return context.mkBV(num, bvBits);
            else
                throw new Error("le numeral " + String.valueOf(num) +
                        " dépasse la capacité des bitvectors signés de taille " +
                        String.valueOf(bvBits));
        } else {
            return context.mkBV(num, bvBits);
        }
    }

    /**
     * Trigger de l'action "pousser un numéral sur la pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr pushNumVar(int step, int num) {
        return boolConst("push_" + String.valueOf(num) + "@" +
                String.valueOf(step));
    }

    /**
     * Trigger de l'action "additionner les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr addVar(int step) {
        return boolConst("add@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "soustraire les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr subVar(int step) {
        return boolConst("sub@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "multiplier les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr mulVar(int step) {
        return boolConst("mul@" + String.valueOf(step));
    }

    /**
     * Trigger de l'action "diviser les deux éléments du dessus de
     * pile et pousser le resultat en dessus de pile" pour le pas
     * d'execution "step" du calcul.
     */
    private BoolExpr divVar(int step) {
        return boolConst("div@" + String.valueOf(step));
    }

    /** Variable d'état représentant la pile au pas d'exécution "step". */
    private ArrayExpr stackStateVar(int step) {
        return arrayConst("stack@" + String.valueOf(step));
    }

    /**
     * Variable d'état représentant l'indice de dessus de pile au pas
     * d'exécution "step".
     */
    private IntExpr idxStateVar(int step) {
        return intConst("idx@" + String.valueOf(step));
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "push(num)".
     */
    private BoolExpr pushNumFormula(int step, int num) {
        // Get the current state of the stack and the index
        ArrayExpr stack = stackStateVar(step);
        BitVecExpr idx = idxStateVar(step);

        // Get the next state of the stack and the index
        ArrayExpr nextStack = stackStateVar(step + 1);
        BitVecExpr nextIdx = idxStateVar(step + 1);

        // Create a boolean variable for the push action
        BoolExpr pushAction = pushVar(step, num);

        // Create a formula that represents pushing num onto the stack
        BoolExpr pushFormula = ctx.mkAnd(
                // The action of pushing num is taken
                pushAction,
                // The next index is the current index + 1
                ctx.mkEq(nextIdx, ctx.mkBVAdd(idx, toBvNum(1))),
                // The next stack is the same as the current stack, except at the next index,
                // where it's num
                ctx.mkEq(nextStack, ctx.mkStore(stack, idx, toBvNum(num))),
                // The number num can only be used once
                ctx.mkNot(ctx.mkOr(usedNumVar(step, num))));

        return pushFormula;
    }

    private interface ActionVar {
        /**
         * Retourne la variable trigger de l'action au step donné.
         */
        BoolExpr get(int step);
    }

    private interface ActionResult {
        /**
         * Retourne l'expression du résultat de l'action au step donné
         * en fonction de e1 et e2, les deux valeurs du dessus de la pile.
         */
        BitVecExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }

    private interface ActionPrecondition {
        /**
         * Retourne l'expression de la précondition de l'action au step
         * donné en fonction de e1 et e2, les deux valeurs du dessus de
         * la pile.
         */
        BoolExpr get(int step, BitVecExpr e1, BitVecExpr e2);
    }


    private BoolExpr actionFormula(int step, ActionVar actVar, ActionPrecondition precond, ActionResult opRes) {
        BoolExpr _result;

        ArrayExpr s = stackStateVar (step);
        IntExpr i = idxStateVar (step);
        
        ArrayExpr next_s = stackStateVar (step + 1);
        IntExpr next_i = idxStateVar (step + 1);
    
        _result = context.mkGe(i, context.mkInt(2));
    
        IntExpr addressV1 = (IntExpr) context.mkSub(i,context.mkInt(1));
        IntExpr addressV2 = (IntExpr) context.mkSub(i,context.mkInt(2));
        BitVecExpr v1 = (BitVecExpr) context.mkSelect(s, addressV1); 
        BitVecExpr v2 = (BitVecExpr) context.mkSelect(s, addressV2);
        
        BoolExpr action = actVar.get(step);
        _result = context.mkAnd(_result, precond.get(step, v1, v2));
        _result = context.mkImplies(action, _result);
    
        BitVecExpr post = opRes.get(step + 1, v1, v2); 
        BoolExpr checkPost = context.mkEq(next_s, context.mkStore(s, context.mkSub(i, context.mkInt(2)),post));
        _result = context.mkAnd(checkPost, context.mkEq(next_i, context.mkSub(i, context.mkInt(1))));
    
        // If noOverflows is true, add an additional check for overflows.
        if (this.noOverflows) {
            BoolExpr noOverflow = context.mkBVAddNoOverflow(v1, v2, false);
            _result = context.mkAnd(_result, noOverflow);
        }
    
        _result = context.mkImplies(action, _result); 
        return _result;
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "addition".
     */
    private BoolExpr addFormula(int step) {
        ActionVar a = this::addVar;
        ActionPrecondition p = (BitVecExpr v1, BitVecExpr v2) -> context.mkTrue();
        ActionResult r = (int stepPlus1, BitVecExpr v1, BitVecExpr v2) -> {
            BoolExpr noOverflow = this.noOverflows ? context.mkBVAddNoOverflow(v1, v2, false) : context.mkTrue();
            return context.mkITE(noOverflow, context.mkBVAdd(v1, v2), context.mkBV(0, bvBits));
        };
        return actionFormula(step, a, p, r);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "soustraction".
     */
    private BoolExpr subFormula(int step) {
        ActionVar a = this::subVar;
        ActionPrecondition p = (BitVecExpr v1, BitVecExpr v2) -> context.mkTrue();
        ActionResult r = (int stepPlus1, BitVecExpr v1, BitVecExpr v2) -> {
            BoolExpr noUnderflow = this.noOverflows ? context.mkBVSubNoUnderflow(v1, v2, false) : context.mkTrue();
            return context.mkITE(noUnderflow, context.mkBVSub(v1, v2), context.mkBV(0, bvBits));
        };
        return actionFormula(step, a, p, r);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "multiplication".
     */
    private BoolExpr mulFormula(int step) {
        ActionVar a = this::mulVar;
        ActionPrecondition p = (BitVecExpr v1, BitVecExpr v2) -> context.mkTrue();
        ActionResult r = (int stepPlus1, BitVecExpr v1, BitVecExpr v2) -> {
            BoolExpr noOverflow = this.noOverflows ? context.mkBVMulNoOverflow(v1, v2, false) : context.mkTrue();
            return context.mkITE(noOverflow, context.mkBVMul(v1, v2), context.mkBV(0, bvBits));
        };
        return actionFormula(step, a, p, r);
    }

    /**
     * Formule de transition, vraie ssi l'état au pas step et au pas
     * step + 1 sont liés par une action "division".
     */
    private BoolExpr divFormula(int step) {
        ActionVar a = this::divVar;
        ActionPrecondition p = (BitVecExpr v1, BitVecExpr v2) -> context.mkNot(context.mkEq(v2, context.mkBV(0, bvBits)));
        ActionResult r = (int stepPlus1, BitVecExpr v1, BitVecExpr v2) -> {
            BoolExpr noUnderflow = this.noOverflows ? context.mkBVSDivNoUnderflow(v1, v2, false) : context.mkTrue();
            return context.mkITE(noUnderflow, context.mkBVSDiv(v1, v2), context.mkBV(0, bvBits));
        };
        return actionFormula(step, a, p, r);
    }

    /**
     * Tableau contenant tous les triggers d'actions push, mul,
     * div, add, sub au pas "step".
     */
    private BoolExpr[] allActions(int step) {
        ArrayList<BoolExpr> arr = new ArrayList<>();

        for (int num : nums) {
            arr.add(pushNumVar(step, num));
        }

        arr.add(mulVar(step));
        arr.add(divVar(step));
        arr.add(addVar(step));
        arr.add(subVar(step));

        return arr.stream().toArray(BoolExpr[]::new);
    }

    /**
     * Formule vraie ssi les états aux pas step et step+1 sont liés par
     * une transition d'action.
     */
    private BoolExpr transitionFormula(int step) {
        BoolExpr _result;

        // Create a list of all possible actions
        BoolExpr[] actions = allActions(step);
    
        // Create a formula that represents exactly one action being executed
        _result = ctx.mkOr(actions);
        for (int i = 0; i < actions.length; i++) {
            for (int j = i + 1; j < actions.length; j++) {
                _result = ctx.mkAnd(_result, ctx.mkNot(ctx.mkAnd(actions[i], actions[j])));
            }
        }
    
        // Combine the action formulas with the transition formulas
        for (int num : numbers) {
            _result = ctx.mkAnd(_result, pushNumFormula(step, num));
        }
        _result = ctx.mkAnd(_result, addFormula(step));
        _result = ctx.mkAnd(_result, subFormula(step));
        _result = ctx.mkAnd(_result, mulFormula(step));
        _result = ctx.mkAnd(_result, divFormula(step));
    
        return _result;
    }

    /**
     * Formule vraie ssi la pile est dans son état initial (au pas 0,
     * toutes les cellules à zéro et dessus de pile à zero).
     */
    private BoolExpr initialStateFormula() {
        // The initial state of the stack is an empty stack, represented by a Z3 array where all elements are zero.
        ArrayExpr initialStack = ctx.mkConst("initialStack", ctx.mkArraySort(ctx.mkIntSort(), ctx.mkBitVecSort(bvBits)));
        BoolExpr stackInit = ctx.mkForall(new Expr[] {ctx.mkIntConst("i")}, 
                                        ctx.mkEq(ctx.mkSelect(initialStack, ctx.mkIntConst("i")), ctx.mkBV(0, bvBits)), 
                                        1, null, null, null, null);

        // The initial state of the stack pointer is zero.
        BoolExpr idxInit = ctx.mkEq(idxStateVar(0), ctx.mkInt(0));

        // The initial state formula is the conjunction of the stack and stack pointer initial state formulas.
        return ctx.mkAnd(stackInit, idxInit);
    }

    /**
     * Formule vraie ssi la pile ne contient qu'un élément qui est égal
     * à la valeur cible au pas "step".
     */
    private BoolExpr finalStateFormula(int step) {
        // The final state of the stack pointer is one.
        BoolExpr idxFinal = context.mkEq(idxStateVar(step), context.mkInt(1));

        // The final state of the stack is a stack where the top element is the expected value.
        BitVecExpr topOfStack = (BitVecExpr) context.mkSelect(stackStateVar(step), context.mkInt(0));
        BoolExpr stackFinal = context.mkEq(topOfStack, context.mkBV(this.target, bvBits));

        // The final state formula is the conjunction of the stack and stack pointer final state formulas.
        return context.mkAnd(idxFinal, stackFinal);
    }

    /**
     * Algorithme de résolution exacte. Déroule une boucle de
     * model-checking borné de la relation de transition depuis l'état
     * initial sur au plus maxNofSteps. Pour chaque itération de
     * model-checking, on ajoute une formule de transition pour le step
     * suivant dans le solveur, on pousse la formule d'état final, on
     * lance une résolution. Si le problème est SAT, on imprime la
     * solution, si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème est UNSAT
     * pour toutes les itérations, on retourne le status UNSAT.
     */
    private Status solveExact(int timeout) {
        Solver solver = context.mkSolver();
        solver.add(initialStateFormula());

        if (timeout > 0) {
            Params p = context.mkParams();
            p.add("timeout", timeout);
            solver.setParameters(p);

            System.out.println("\n\nsolveExact with timeout " +
                            String.valueOf(timeout));
        } else {
            System.out.println("\n\nsolveExact without timeout" );
        }

        // Start with one step and increment until a solution is found or the maximum number of steps is reached.
        for (int step = 1; step <= maxNofSteps; step++) {
            // Add the transition formula for the current step.
            solver.add(transitionFormula(step));

            // Check if there is a solution with the current number of steps.
            if (solver.check() == Status.SATISFIABLE) {
                // If a solution is found, return SATISFIABLE.
                return Status.SATISFIABLE;
            }
        }

        // If no solution is found within the maximum number of steps, return UNSATISFIABLE.
        return Status.UNSATISFIABLE;
    }

    /**
     * Formule vraie ssi la pile n'est pas dans son état final au pas
     * "step".
     */
    private BoolExpr finalStateApproxFormula(int step) {
        // The final state of the stack pointer is one.
        BoolExpr idxFinal = context.mkEq(idxStateVar(step), context.mkInt(1));

        // The final state of the stack is a stack where the top element is not the expected value.
        BitVecExpr topOfStack = (BitVecExpr) context.mkSelect(stackStateVar(step), context.mkInt(0));
        BoolExpr stackFinal = context.mkNot(context.mkEq(topOfStack, context.mkBV(this.target, bvBits)));

        // The final state formula is the conjunction of the stack and stack pointer final state formulas.
        return context.mkAnd(idxFinal, stackFinal);
    }

    /**
     * Critère d'optimisation, écart en valeur absolue entre la valeur
     * du dessus de la pile et la valeur cible au pas "step".
     */
    private BitVecExpr finalStateApproxCriterion(int step) {
        // The top of the stack at the final step.
        BitVecExpr topOfStack = (BitVecExpr) context.mkSelect(stackStateVar(step), context.mkInt(0));

        // The absolute difference between the top of the stack and the target value.
        return context.mkBVSub(context.mkBV(this.target, bvBits), topOfStack);
    }

    /**
     * Algorithme de résolution approchée par optimisation max-SMT. À
     * chaque étape de BMC, on minimise la distance à la cible. Le
     * solveur d'optimisation n'est pas incrémental donc push et pop ne
     * sont pas disponibles, on instancie donc un nouveau solveur et
     * toutes les contraintes jusqu'au pas "step" à chaque itération,
     * ainsi que le critère à optimiser. Pour chaque itération le
     * problème est sensé être SAT et on imprime la solution à chaque
     * itération. Si le problème est UNSAT, on retire la formule d'état
     * final et on passe à l'itération suivante. Si le problème est
     * UNKNOWN, on retourne le status UNKOWN. Si le problème était SAT
     * pour toutes les itérations, on retourne le status SAT.
     */
    private Status solveApprox(int timeout) {

        // ce solver n'est pas incrémental, il faut le recréer à
        // chaque nouvelle itération du BMC.
        // utiliser les méthodes suivantes sur le solveur (attention
        // aux majuscules !) :
        // - Add pour ajouter une formule
        // - MkMinimize pour ajouter un critère à optimiser
        // - Check pour résoudre
        Optimize solver = context.mkOptimize();

        if (timeout > 0) {
            Params p = context.mkParams();
            p.add("timeout", timeout);
            solver.setParameters(p);
        }
    
        // Add the initial state formula.
        solver.Add(initialStateFormula());
    
        // Start with one step and increment until a solution is found or the maximum number of steps is reached.
        for (int step = 1; step <= maxNofSteps; step++) {
            // Add the transition formula for the current step.
            solver.Add(transitionFormula(step));
    
            // Add the final state approximation formula as a constraint.
            solver.Add(finalStateApproxFormula(step));
    
            // Minimize the approximation criterion.
            solver.MkMinimize(finalStateApproxCriterion(step));
    
            // Check if there is a solution with the current number of steps.
            if (solver.Check() == Status.SATISFIABLE) {
                // If a solution is found, return SATISFIABLE.
                return Status.SATISFIABLE;
            }
        }
    
        // If no solution is found within the maximum number of steps, return UNSATISFIABLE.
        return Status.UNSATISFIABLE;
    }

    /**
     * Résout le problème en essayant une résolution exacte,
     * puis une résolution approximative en cas d'échec.
     */
    Status solve(int timeout) {
        printParams();

        Status s = solveExact(timeout);

        if (s != Status.SATISFIABLE) {
            s = solveApprox(timeout);
        }

        return s;
    }

    /** Affiche le contenu de la pile en ASCII sur sdtout. */
    private void printStackAtStep(Model m, int step) {
        for (int idx = 0; idx <= maxNofSteps; idx++) {
            BitVecExpr resbv =
                (BitVecExpr) context.mkSelect(stackStateVar(step),
                                              context.mkInt(idx));
            IntExpr resi = context.mkBV2Int(resbv, true);

            if (m.eval(context.mkEq(idxStateVar(step),
                                    context.mkInt(idx)), true).isTrue()) {
                System.out.print(" <| ");
            } else {
                System.out.print(" | ");
            }

            System.out.print(m.eval(resi, true));
        }

        System.out.println();
    }

    /**
     * Affiche le contenu d'un modèle m obtenu par BMC jusqu'à
     * la profondeur steps.
     */
    private void printModel(Model m, int steps) {
        System.out.print("init ~> ");
        printStackAtStep(m, 0);

        for (int step = 0; step <= steps; step++) {
            for (int num : nums) {
                if (m.eval(pushNumVar(step, num), true).isTrue()) {
                    System.out.print("push " + String.valueOf(num) + " ~> ");
                }
            }

            if (m.eval(mulVar(step), true).isTrue()) {
                System.out.print("mul ~> ");
            }

            if (m.eval(divVar(step), true).isTrue()) {
                System.out.print("div ~> ");
            }

            if (m.eval(addVar(step), true).isTrue()) {
                System.out.print("add ~> ");
            }

            if (m.eval(subVar(step), true).isTrue()) {
                System.out.print("sub ~> ");
            }

            printStackAtStep(m, step + 1);
        }
    }

    private void printParams() {
        System.out.println("\nParameters:");
        System.out.println("- bvBits     : " + String.valueOf(bvBits));
        System.out.println("- noOverflows: " + String.valueOf(noOverflows));
        System.out.println("- nums       : " + Arrays.toString(nums));
        System.out.println("- target     : " + String.valueOf(target));
    }
}

/* Réponses aux questions du sujet */

/*
 * 1. Combien d’étapes de calcul peut-il y avoir au plus en fonction du nombre
 * de constantes données en entrée ?
 * Étant donné N constantes, chaque constante peut être utilisée exactement une
 * fois, de sorte qu'il y ait N étapes pour pousser chaque constante sur la
 * pile.
 * Étant donné qu'une opération nécessite deux constantes, le nombre maximal
 * d'opérations pouvant être effectuées est N-1.
 * Par conséquent, le nombre maximal d'étapes de calcul est N (pour
 * l'introduction des constantes) + N-1 (pour les opérations) = 2N - 1.
 */
