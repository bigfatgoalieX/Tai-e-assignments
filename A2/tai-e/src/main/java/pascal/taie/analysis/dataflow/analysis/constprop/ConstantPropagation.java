/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();

        for(Var param : cfg.getIR().getParams()){
            if(canHoldInt(param)){
                fact.update(param, Value.getNAC());
            }
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var v : fact.keySet()){
            Value oldValue = target.get(v);
            Value newValue = meetValue(oldValue, fact.get(v));
            target.update(v, newValue);
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        if(v1.isUndef()){
            return v2;
        }
        if(v2.isUndef()){
            return v1;
        }
        if(v1.isConstant() && v2.isConstant()){
            if(v1.getConstant() == v2.getConstant()){
                return v1;
            }
            else{
                return Value.getNAC();
            }
        }

        // with caution
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();

        if(stmt instanceof DefinitionStmt<?,?> defstmt){
            LValue lvalue = defstmt.getLValue();
            RValue rvalue = defstmt.getRValue();

            // when "x=m(...)" or "x=o.f" , i.e. right side is not a "exp" we wanted now
            // evaluate() returns NAC then
            Value rvalue_evaluated = evaluate(rvalue,in);

            if(lvalue instanceof Var var && canHoldInt(var)){
                newOut.update(var, rvalue_evaluated);
            }
            // for lvalue like "o.f = ..." nothing should be done
            // just the identity map from IN -> OUT
            // which has been done in the first line
        }
        if(!newOut.equals(out)){
            out.copyFrom(newOut);
            return true;
        }
        return false;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if(exp instanceof Var){
            return in.get((Var) exp);
        }

        if(exp instanceof IntLiteral){
            return Value.makeConstant(((IntLiteral)exp).getValue());
        }

        if(exp instanceof BinaryExp){
            BinaryExp bexp = (BinaryExp) exp;
            Value lvalue = evaluate(bexp.getOperand1(), in);
            Value rvalue = evaluate(bexp.getOperand2(), in);

            // 3 different conditions
            if(lvalue.isNAC() || rvalue.isNAC()){
                return Value.getNAC();
            }
            if(lvalue.isUndef() || rvalue.isUndef()){
                return Value.getUndef();
            }

            if(lvalue.isConstant() && rvalue.isConstant()){
                int a = lvalue.getConstant();
                int b = rvalue.getConstant();

                // to handle different kinds of binary expressions

                // ArithmeticExp
                if(bexp instanceof ArithmeticExp){
                    ArithmeticExp.Op op = ((ArithmeticExp)bexp).getOperator();
                    switch(op){
                        case ADD: return Value.makeConstant(a + b);
                        case SUB: return Value.makeConstant(a - b);
                        case MUL: return Value.makeConstant(a * b);
                        case DIV: return b==0 ? Value.getUndef() : Value.makeConstant(a / b);
                        case REM: return b==0 ? Value.getUndef() : Value.makeConstant(a % b);
                        default:
                            throw new AssertionError("Unknown arithmetic operator: " + op);
                    }
                }
                // BitwiseExp
                if(bexp instanceof BitwiseExp){
                    BitwiseExp.Op op = ((BitwiseExp)bexp).getOperator();
                    switch(op){
                        case OR: return Value.makeConstant(a | b);
                        case AND: return Value.makeConstant(a & b);
                        case XOR: return Value.makeConstant(a ^ b);
                        default:
                            throw new AssertionError("Unknown bitwise operator: " + op);
                    }
                }
                // ConditionalExp
                if(bexp instanceof ConditionExp){
                    ConditionExp.Op op = ((ConditionExp)bexp).getOperator();
                    switch(op){
                        case EQ: return (a==b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case NE: return (a!=b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LT: return (a<b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GT: return (a>b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case LE: return (a<=b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        case GE: return (a>=b) ? Value.makeConstant(1) : Value.makeConstant(0);
                        default:
                            throw new AssertionError("Unknown condition operator: " + op);
                    }
                }
                // ShiftExp
                if(bexp instanceof ShiftExp){
                    ShiftExp.Op op = ((ShiftExp)bexp).getOperator();
                    switch(op){
                        case SHL: return Value.makeConstant(a << b);
                        case SHR: return Value.makeConstant(a >> b);
                        case USHR: return Value.makeConstant(a >>> b);
                        default:
                            throw new AssertionError("Unknown shift operator: " + op);
                    }
                }
                // just in case
                return Value.getNAC();
            }
            // just in case
            return Value.getNAC();
        }
        // when right side exp is not Var or IntLiteral or BinaryExp
        return Value.getNAC();
    }
}
