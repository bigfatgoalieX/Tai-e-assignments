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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;
import java.util.ArrayDeque;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // nodes which are reachable
        // initially empty
        Set<Stmt> reachable = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // nodes to be processed
        ArrayDeque<Stmt> worklist = new ArrayDeque<>();
        // initially only the Entry node
        worklist.add(cfg.getEntry());

        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.poll();
            if(reachable.contains(stmt)) {
                continue;
            }
            // say the current node is reachable
            reachable.add(stmt);
            // then add all its possible successors into the worklist
            // some paths (If or Switch) are considered invalid
            for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                Stmt target = edge.getTarget();
                boolean valid = true;

                // if stmt
                if(stmt instanceof If ifstmt){
                    Value conditionvalue = ConstantPropagation.evaluate(ifstmt.getCondition(),constants.getInFact(stmt));

                    if(conditionvalue.isConstant()){
                        boolean cond_is_false = (conditionvalue.getConstant() == 0);
                        if(edge.getKind() == Edge.Kind.IF_TRUE && cond_is_false){
                            valid = false;
                        }
                        if(edge.getKind() == Edge.Kind.IF_FALSE && !cond_is_false){
                            valid = false;
                        }
                    }
                }

                // switch stmt
                if(stmt instanceof SwitchStmt switchstmt){
                    Value conditionvalue = ConstantPropagation.evaluate(switchstmt.getVar(),constants.getInFact(stmt));

                    if(conditionvalue.isConstant()){
                        int constvalue = conditionvalue.getConstant();
                        if(edge.getKind() == Edge.Kind.SWITCH_CASE){
                            if(!edge.isSwitchCase()){
                                continue;
                            }
                            if(edge.getCaseValue() != constvalue){
                                valid = false;
                            }
                        }
                        if(edge.getKind() == Edge.Kind.SWITCH_DEFAULT){
                            boolean anyMatch = false;
                            for(int x : switchstmt.getCaseValues()){
                                if(x == constvalue){
                                    anyMatch = true;
                                    break;
                                }
                            }
                            if(anyMatch){
                               valid = false;
                            }
                        }
                        // no need to handle FALL_THROUGH edges separately
                        // draw a demo you'll see
                    }
                }

                if(valid){
                    worklist.add(target);
                }
            }
        }


        for(Stmt stmt : cfg){
            // don't add Exit node into deadCode Set
            // for example, in the testcase "Loops"
            // you never reach the Exit node
            // But you don't want it in the deadCode Set
            if(!reachable.contains(stmt) && !cfg.isExit(stmt)){
                deadCode.add(stmt);
            }
        }

        for(Stmt stmt : reachable){
            if(stmt instanceof AssignStmt<?,?> assignstmt){
                if(assignstmt.getLValue() instanceof Var var){
                    SetFact<Var> out = liveVars.getOutFact(stmt);
                    if(!out.contains(var) && hasNoSideEffect(assignstmt.getRValue())){
                        deadCode.add(stmt);
                    }
                }
            }
        }

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
