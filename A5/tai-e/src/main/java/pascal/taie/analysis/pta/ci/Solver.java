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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Assign;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(callGraph.contains(method)) {
            return;
        }

        callGraph.addReachableMethod(method);

        for(var stmt : method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) { // x = new T()
            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            PointsToSet pointsToSet = new PointsToSet(obj);
            workList.addEntry(x, pointsToSet);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) { // x = y
            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr y = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(y,x);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadArray stmt) { // nothing to do
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreArray stmt) { // nothing to do
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(LoadField stmt) { // y = T.f
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                VarPtr y = pointerFlowGraph.getVarPtr(stmt.getLValue());
                StaticField T_f = pointerFlowGraph.getStaticField(field);
                addPFGEdge(T_f,y);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) { // T.f = y
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                StaticField T_f = pointerFlowGraph.getStaticField(field);
                VarPtr y = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(y,T_f);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Invoke stmt) { // x = T.m(...)
            // build callGraph if needed
            // for PFG:
            // actual_i -> formal_i
            // return -> x
            if(stmt.isStatic()){
                JMethod callee = resolveCallee(null,stmt);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC,stmt,callee))){ // if callGraph changes
                    addReachable(callee);
                    InvokeExp invokeExp = stmt.getInvokeExp(); // get the invoke expression
                    for(int i = 0; i < invokeExp.getArgCount(); i++) {
                        VarPtr actual_i = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                        VarPtr formal_i = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                        addPFGEdge(actual_i,formal_i);
                    }
                    if(stmt.getLValue()!=null){ // there is an x
                        for(Var returnVar : callee.getIR().getReturnVars()){
                            VarPtr return_i = pointerFlowGraph.getVarPtr(returnVar);
                            VarPtr x = pointerFlowGraph.getVarPtr(stmt.getLValue());
                            addPFGEdge(return_i,x);
                        }
                    }
                }
            }
            return StmtVisitor.super.visit(stmt);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)){
            if(!source.getPointsToSet().isEmpty()){
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry(); //entry = <n,pts>
            Pointer n = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(n,pts); // \delta = pts - pt(n)
            if(n instanceof VarPtr varPtr) {
                Var x = varPtr.getVar();
                for(Obj obj : delta){
                    for(StoreField storeField : x.getStoreFields()){ // x.f = y
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField x_f = pointerFlowGraph.getInstanceField(obj, field);
                        VarPtr y = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(y,x_f);
                    }
                    for(LoadField loadField : x.getLoadFields()){ // y = x.f
                        JField field = loadField.getFieldRef().resolve();
                        VarPtr y = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        InstanceField x_f = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(x_f,y);
                    }
                    for(StoreArray storeArray : x.getStoreArrays()){ // x[i] = y
                        ArrayIndex x_i = pointerFlowGraph.getArrayIndex(obj);
                        VarPtr y = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(y,x_i);
                    }
                    for(LoadArray loadArray : x.getLoadArrays()){ // y = x[i]
                        VarPtr y = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        ArrayIndex x_i = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(x_i,y);
                    }
                    processCall(x,obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    // two steps in one function
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        // input (n,pts)
        PointsToSet delta = new PointsToSet();
        for(Obj obj : pointsToSet){ // obj in pts
            if(!pointer.getPointsToSet().contains(obj)){ // obj not in pt(n)
                delta.addObject(obj); // hence the difference
                pointer.getPointsToSet().addObject(obj);
            }
        }
        if(!delta.isEmpty()){
            for(Pointer succ : pointerFlowGraph.getSuccsOf(pointer)){
                workList.addEntry(succ,delta);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke invoke : var.getInvokes()){
            JMethod callee = resolveCallee(recv,invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(callee.getIR().getThis()),new PointsToSet(recv));

            boolean changed = false;
            if(invoke.isVirtual()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.VIRTUAL,invoke,callee));
            } else if (invoke.isInterface()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.INTERFACE,invoke,callee));
            } else if (invoke.isSpecial()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.SPECIAL,invoke,callee));
            }
            if(changed){
                addReachable(callee);
                InvokeExp invokeExp = invoke.getInvokeExp(); // get the invoke expression
                for(int i = 0; i < invokeExp.getArgCount(); i++) {
                    VarPtr actual_i = pointerFlowGraph.getVarPtr(invokeExp.getArg(i));
                    VarPtr formal_i = pointerFlowGraph.getVarPtr(callee.getIR().getParam(i));
                    addPFGEdge(actual_i,formal_i);
                }
                if(invoke.getLValue()!=null){
                    for(Var returnVar : callee.getIR().getReturnVars()){
                        VarPtr return_i = pointerFlowGraph.getVarPtr(returnVar);
                        VarPtr x = pointerFlowGraph.getVarPtr(invoke.getLValue());
                        addPFGEdge(return_i,x);
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
