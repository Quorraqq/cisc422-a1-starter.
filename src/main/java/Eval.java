import ast.*;
import java.util.*;

public class Eval extends BaseEval {
    //-----------------------!! DO NOT MODIFY !!-------------------------
    private int[][] M;
    public Eval(int[][] M) {
        this.M = M;
    }
    //-------------------------------------------------------------------
    @Override
    protected Integer evalNExp(NExp exp, Env env) {
        if (exp instanceof Nat){
            return ((Nat) exp).value;
        } else if (exp instanceof SalesForM) {
            return SalesForM( (SalesForM) exp,  env);
        } else if (exp instanceof SalesAt) {
            return SalesAt( (SalesAt) exp, env);
        } else if (exp instanceof SalesForP) {
            return SalesForP( (SalesForP) exp, env);
        } else if (exp instanceof SalesForD){
            return SalesForD( (SalesForD) exp, env);
        }else if (exp instanceof BinaryNExp){
            return BinaryNExp( (BinaryNExp) exp,env);
        } else if (exp instanceof  Var) {
            return Var( (Var) exp, env);
        } else if (exp instanceof Size) {
            return Size((Size) exp, env);
        }
        return  0;
    }
    @Override
    protected Set<Integer> evalSExp(SExp exp, Env env) {
        if (exp instanceof BinarySExp) {
            return BinarySExp( (BinarySExp) exp, env);
        }  else if (exp instanceof Type){
            return Type((Type) exp, env);
        }else if (exp instanceof SetCompr){
            return SetCompr( (SetCompr) exp, env);
        }
        return null;}
    @Override
    protected Boolean evalFormula(Formula formula, Env env) {
        if (formula instanceof AtomicN){
            return AtomicN((AtomicN) formula,  env);
        } else if (formula instanceof AtomicS){
            return AtomicS((AtomicS) formula, env);
        }else if (formula instanceof Unary){
            return Unary( (Unary) formula, env);
        }else if (formula instanceof  Binary){
            return Binary( (Binary) formula, env);
        }else if (formula instanceof Quantified){
            return Quantified( (Quantified) formula, env);
        }
        return false;
    }
    public boolean Quantified(Quantified formula, Env env) {
        String name = formula.var.name;
        int setSize = evalSExp(formula.type, env).size();
        if (formula.quantifier.kind == Quantifier.EXISTS().kind) {
            boolean compar = false;
            for (int a = 1; a <= setSize; a++) {
                env.push(name, a);
                compar = compar | evalFormula(formula.formula, env);
                env.pop();
                if (compar) {
                    break;  // Early exit if compar is true since further OR operations will not change the result
                }
            }
            return compar;
        } else if (formula.quantifier.kind == Quantifier.FORALL().kind) {
            boolean compar = true;
            for (int a = 1; a <= setSize; a++) {
                env.push(name, a);
                compar = compar & evalFormula(formula.formula, env);
                env.pop();
                if (!compar) {
                    break;  // Early exit if compar is false since further AND operations will not change the result
                }
            }
            return compar;
        }
        return false;
    }
    public int SalesForM(SalesForM exp, Env env){
        int sum = 0;
        for (int a = 0; a < M.length; a++) {// Assuming M is a 2D array defined elsewhere
            for (int b = 0; b < M[a].length; b++) {
                sum += M[a][b];
            }
        }
        return sum;
    }
    public Set<Integer>Type(Type exp, Env env){
        Set<Integer> set = new HashSet<>();
        if (exp.kind == Type.Kind.DAY) { // 5 days, 1~5
            for (int a = 1; a <= 5; a++) {
                set.add(a);
            }
        }
        else if (exp.kind == Type.Kind.SALE) { //add all entries in the array without duplicate
            for (int[] ints : M) {
                for (int value : ints) {
                    set.add(value);
                }
            }
        }
        else if (exp.kind == Type.Kind.PRODUCT) { // 4 prods, 1~4
            for (int a = 1; a <= 4; a++) {
                set.add(a);
            }
        }
        return set;
    }
    public boolean AtomicN(AtomicN formula, Env env){
        int lhsValue = evalNExp(formula.lhs, env);// Calculate the values on the left and right sides of the formula
        int rhsValue = evalNExp(formula.rhs, env);
        RelNOp.Kind kind = formula.relNOp.kind;// Get the type of operator
        return performComparison(kind, lhsValue, rhsValue);// Perform the comparison based on the operator type and return the result
    }
    private boolean performComparison(RelNOp.Kind kind, int lhsValue, int rhsValue) {
        if(kind == RelNOp.EQ().kind) {// "="
            return lhsValue == rhsValue;
        }
        else if (kind == RelNOp.NEQ().kind) {// "!="
            return lhsValue != rhsValue;
        }
        else if (kind == RelNOp.GT().kind) {// ">"
            return lhsValue > rhsValue;
        }
        else if (kind == RelNOp.GTE().kind) {// ">="
            return lhsValue >= rhsValue;
        }
        else if (kind == RelNOp.LT().kind) {// "<"
            return lhsValue < rhsValue;
        }
        else if (kind == RelNOp.LTE().kind) {// "<="
            return lhsValue <= rhsValue;
        }
        else {
            return false;
        }
    }
    public int Size(Size exp, Env env){
        if(exp == null || env == null) {// Check for null before proceeding to prevent NullPointerException
            throw new IllegalArgumentException("Exp and Env cannot be null.");
        }
        return evalSExp(exp.sExp, env).size();// Evaluate the set expression and return its size
    }
    public boolean AtomicS(AtomicS formula, Env env){
        if(formula == null || env == null) {
            throw new IllegalArgumentException("Formula and Env cannot be null.");
        }
        if (formula.relSOp.kind == RelSOp.EQ().kind){
            return evalSExp(formula.lhs, env).equals(evalSExp(formula.rhs, env));
        }
        return false;
    }
    public int SalesForP(SalesForP exp, Env env) {
        // Basic null checks to ensure that objects are not null before accessing their methods/fields
        if(exp == null || env == null) {
            throw new IllegalArgumentException("Exp and Env cannot be null.");
        }
        int sum = 0;
        int productIndex = evalNExp(exp.product, env) - 1;
        for (int a = 0; a < 5; a++) {
            sum += M[productIndex][a];
        }
        return sum;
    }
    public int SalesForD(SalesForD exp, Env env) {
        if(exp == null || env == null) {
            throw new IllegalArgumentException("Exp and Env cannot be null.");
        }
        int sum = 0;
        int dayIndex = evalNExp(exp.day, env) - 1;
        for (int a = 0; a < 4; a++) {
            sum += M[a][dayIndex];
        }
        return sum;
    }
    public int SalesAt(SalesAt exp, Env env){// return reuqired nth row nth column entry
        return M[evalNExp(exp.product,env)-1][evalNExp(exp.day,env)-1];
    }
    public int BinaryNExp(BinaryNExp exp, Env env){
        if (exp.op.kind == BinNOp.ADD().kind){
            return evalNExp(exp.lhs, env) + evalNExp(exp.rhs,env);
        }else if (exp.op.kind == BinNOp.DIFF().kind) {
            return evalNExp(exp.lhs, env) - evalNExp(exp.rhs,env);
        } else if (exp.op.kind == BinNOp.MULT().kind) {
            return evalNExp(exp.lhs, env) * evalNExp(exp.rhs,env);
        }else if (exp.op.kind == BinNOp.DIV().kind) {
            if(evalNExp(exp.rhs,env) == 0){
                throw new BaseEval.DivisionByZeroException();
            }
            return evalNExp(exp.lhs, env) / evalNExp(exp.rhs,env);
        }
        return 0;
    }
    public Set<Integer> BinarySExp( BinarySExp exp, Env env){//operattion between sets
        Set<Integer> result = new HashSet<>();
        if (exp.op.kind == BinSOp.DIFF().kind) {
            result.addAll(evalSExp(exp.lhs,env));
            result.removeAll(evalSExp(exp.rhs,env));
        } else if (exp.op.kind == BinSOp.UNION().kind){
            result.addAll(evalSExp(exp.lhs,env));
            result.addAll(evalSExp(exp.rhs,env));
        } else if (exp.op.kind == BinSOp.INTER().kind){
            result.addAll(evalSExp(exp.lhs,env));
            result.retainAll(evalSExp(exp.rhs,env));
        }
        return result;
    }
    public boolean Binary( Binary formular, Env env){//Binary expressions T/F determent, return boolean
        if (formular.binConn.kind == BinaryConn.IMPLY().kind) {
            return !(evalFormula(formular.lhs,env)) | evalFormula(formular.rhs,env);
        } else if (formular.binConn.kind == BinaryConn.EQUIV().kind){
            return (!(evalFormula(formular.lhs,env)) | evalFormula(formular.rhs,env)) & (!(evalFormula(formular.rhs,env)) | evalFormula(formular.lhs,env));
        } else if (formular.binConn.kind == BinaryConn.OR().kind) {
            return evalFormula(formular.lhs, env) | evalFormula(formular.rhs, env);
        } else if (formular.binConn.kind == BinaryConn.AND().kind){
            return evalFormula(formular.lhs,env) & evalFormula(formular.rhs,env);
        }
        return false;
    }
    public boolean Unary(Unary formula, Env env) {
        System.out.println("Attempting to evaluate unary formula: " + formula);// Log the attempt to evaluate the unary formula
        validateUnaryFormula(formula, env);
        if (formula.unConn.kind == UnaryConn.NOT().kind) {// Check the kind of the unary connection and evaluate the formula accordingly
            boolean evaluationResult = !(evalFormula(formula.formula, env));
            System.out.println("Unary NOT evaluation result: " + evaluationResult);
            return evaluationResult;
        } else {
            System.err.println("Error: Unsupported unary connection kind: " + formula.unConn.kind);
            throw new UnsupportedOperationException("Unsupported unary connection kind.");
        }
    }
    private void validateUnaryFormula(Unary formula, Env env) {
        if (formula == null || env == null) {
            System.err.println("Error: Invalid input encountered. Formula and environment must be non-null.");
            throw new IllegalArgumentException("Invalid input. Formula and environment cannot be null.");
        }
        if (formula.unConn == null || formula.formula == null) {
            System.err.println("Error: Unary formula or connection is null.");
            throw new IllegalArgumentException("Unary formula and connection must be non-null.");
        }
    }
    public int Var(Var exp, Env env) {
        System.out.println("Attempting to retrieve value for variable: " + exp.name);
        validateVarExpression(exp);
        int varValue = env.lookup(exp.name);
        System.out.println("Retrieved value: " + varValue);
        if (varValue == -1) {// If the value was not found, log an error and throw an exception
            System.err.println("Error: Variable not found: " + exp.name);
            throw new BaseEval.UnboundVariableException();
        }
        System.out.println("Successfully retrieved value for variable: " + exp.name);
        return varValue;
    }
    private void validateVarExpression(Var exp) {
        if (exp == null || exp.name == null || exp.name.trim().isEmpty()) {// Check if the expression is valid (e.g., non-null and has a name)
            System.err.println("Error: Invalid variable expression encountered.");
            throw new IllegalArgumentException("Invalid variable expression.");
        }
    }
    public Set<Integer> SetCompr(SetCompr exp, Env env) {
        String name = exp.var.name;
        Set<Integer> set = new HashSet<>();
        int size = evalSExp(exp.type, env).size();
        for (int a = 1; a <= size; a++) {
            env.push(name, a);
            if (evalFormula(exp.formula, env)) { // collect if condition is met
                set.add(a);
            }
            env.pop();
        }
        return set;
    }
}
