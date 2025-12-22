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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(callGraph.contains(csMethod)) {
            return;
        }

        callGraph.addReachableMethod(csMethod);

        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);

        for(var stmt : csMethod.getMethod().getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) { // x = new T()
            CSVar csVar = csManager.getCSVar(context,stmt.getLValue()); // c:x
            Obj obj = heapModel.getObj(stmt); // o
            Context heapContext = contextSelector.selectHeapContext(csMethod,obj); // c of o
            CSObj csObj = csManager.getCSObj(heapContext, obj); // c:o
            PointsToSet pointsToSet = PointsToSetFactory.make(csObj); // {c:o}
            workList.addEntry(csVar, pointsToSet);
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(Copy stmt) { // x = y
            CSVar x = csManager.getCSVar(context,stmt.getLValue());
            CSVar y = csManager.getCSVar(context,stmt.getRValue());
            addPFGEdge(y,x);
            taintAnalysis.addTFGEdge(y,x);
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
                CSVar y = csManager.getCSVar(context,stmt.getLValue());
                StaticField T_f = csManager.getStaticField(field);
                addPFGEdge(T_f,y);
                taintAnalysis.addTFGEdge(T_f,y);
            }
            return StmtVisitor.super.visit(stmt);
        }

        @Override
        public Void visit(StoreField stmt) { // T.f = y
            if(stmt.isStatic()){
                JField field = stmt.getFieldRef().resolve();
                StaticField T_f = csManager.getStaticField(field);
                CSVar y = csManager.getCSVar(context,stmt.getRValue());
                addPFGEdge(y,T_f);
                taintAnalysis.addTFGEdge(y,T_f);
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
                CSCallSite csCallSite = csManager.getCSCallSite(context,stmt);
                Context c_t = contextSelector.selectContext(csCallSite,callee); // c^t
                CSMethod cs_Method = csManager.getCSMethod(c_t,callee); // c^t:m
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC,csCallSite,cs_Method))){ // if callGraph changes
                    addReachable(cs_Method);
                    InvokeExp invokeExp = stmt.getInvokeExp(); // get the invoke expression
                    for(int i = 0; i < invokeExp.getArgCount(); i++) {
                        CSVar actual_i = csManager.getCSVar(context,invokeExp.getArg(i));
                        CSVar formal_i = csManager.getCSVar(c_t,callee.getIR().getParam(i));
                        addPFGEdge(actual_i,formal_i);
                        taintAnalysis.addTFGEdge(actual_i,formal_i);
                    }
                    if(stmt.getLValue()!=null){ // there is an x
                        for(Var returnVar : callee.getIR().getReturnVars()){
                            CSVar return_i = csManager.getCSVar(c_t,returnVar);
                            CSVar x = csManager.getCSVar(context,stmt.getLValue());
                            addPFGEdge(return_i,x);
                            taintAnalysis.addTFGEdge(return_i,x);
                        }
                    }

                    // taint specific rules
                    // x = T.m(...) may generates a taint object
                    if(taintAnalysis.isSource(callee) && stmt.getLValue() != null){
                        CSVar csVar = csManager.getCSVar(context,stmt.getLValue()); // c:x
                        Obj obj = taintAnalysis.makeTaint(stmt,callee.getReturnType()); // t
                        Context heapContext = taintAnalysis.getEmptyContext(); // c of t, which is empty here
                        CSObj csObj = csManager.getCSObj(heapContext,obj); // c:t
                        PointsToSet pointsToSet = PointsToSetFactory.make(csObj); // {c:t}
                        workList.addEntry(csVar, pointsToSet);
                    }
                    // the callee may have a match in set TaintTransfer(<m,from,to,u>)
                    // in this case, need to addTFGEdge
                    taintAnalysis.TaintTransfer(stmt,callee,null,context);
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
        if(pointerFlowGraph.addEdge(source, target)) {
            if(!source.getPointsToSet().isEmpty()) {
                PointsToSet setofregularobj = PointsToSetFactory.make();
                for(CSObj csObj : source.getPointsToSet()) {
                    // on PFG, only deal with o_i and ignore t_i
                    if(!taintAnalysis.isTaint(csObj.getObject())) {
                        setofregularobj.addObject(csObj);
                    }
                }
                if(!setofregularobj.isEmpty()) {
                    workList.addEntry(target, setofregularobj);
                }
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
            if(n instanceof CSVar csVar) {
                Var x = csVar.getVar();
                for(CSObj csObj : delta){
                    for(StoreField storeField : x.getStoreFields()){ // x.f = y
                        JField field = storeField.getFieldRef().resolve();
                        InstanceField x_f = csManager.getInstanceField(csObj,field);
                        CSVar y = csManager.getCSVar(csVar.getContext(),storeField.getRValue());
                        addPFGEdge(y,x_f);
                        taintAnalysis.addTFGEdge(y,x_f);
                    }
                    for(LoadField loadField : x.getLoadFields()){ // y = x.f
                        JField field = loadField.getFieldRef().resolve();
                        CSVar y = csManager.getCSVar(csVar.getContext(),loadField.getLValue());
                        InstanceField x_f = csManager.getInstanceField(csObj,field);
                        addPFGEdge(x_f,y);
                        taintAnalysis.addTFGEdge(x_f,y);
                    }
                    for(StoreArray storeArray : x.getStoreArrays()){ // x[i] = y
                        ArrayIndex x_i = csManager.getArrayIndex(csObj);
                        CSVar y = csManager.getCSVar(csVar.getContext(),storeArray.getRValue());
                        addPFGEdge(y,x_i);
                        taintAnalysis.addTFGEdge(y,x_i);
                    }
                    for(LoadArray loadArray : x.getLoadArrays()){ // y = x[i]
                        CSVar y = csManager.getCSVar(csVar.getContext(),loadArray.getLValue());
                        ArrayIndex x_i = csManager.getArrayIndex(csObj);
                        addPFGEdge(x_i,y);
                        taintAnalysis.addTFGEdge(x_i,y);
                    }
                    if(!taintAnalysis.isTaint(csObj.getObject())){
                        processCall(csVar,csObj);
                    }
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet delta = PointsToSetFactory.make();
        // use factory rather than constructor to initialize a new PointsToSet
        for(CSObj obj : pointsToSet) {
            if(!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
                pointer.getPointsToSet().addObject(obj);
            }
        }
        // delta = {o1,o2,...,t1,t2,...}
        // delta_o = {o1,o2,...}
        // delta_t = {t1,t2,...}
        PointsToSet delta_o = PointsToSetFactory.make();
        PointsToSet delta_t = PointsToSetFactory.make();
        for(CSObj csObj : delta.getObjects()) {
            if(taintAnalysis.isTaint(csObj.getObject())) {
                delta_t.addObject(csObj);
            }else {
                delta_o.addObject(csObj);
            }
        }

        if(!delta_o.isEmpty()) {
            for(Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ,delta_o);
            }
        }
        if(!delta_t.isEmpty()) {
            for(Pointer succ : taintAnalysis.getSuccsOf(pointer)) {
                workList.addEntry(succ,delta_t);
            }
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for(Invoke invoke : recv.getVar().getInvokes()){
            JMethod callee = resolveCallee(recvObj,invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(),invoke);
            Context c_t = contextSelector.selectContext(csCallSite,recvObj,callee); // c^t = Select(...)
            CSVar m_this = csManager.getCSVar(c_t,callee.getIR().getThis());
            workList.addEntry(m_this,PointsToSetFactory.make(recvObj)); // add <c^t:m_this,{c':o_i}> to WL

            boolean changed = false;
            CSMethod csMethod = csManager.getCSMethod(c_t,callee);
            if(invoke.isVirtual()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.VIRTUAL,csCallSite,csMethod));
            } else if (invoke.isInterface()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.INTERFACE,csCallSite,csMethod));
            } else if (invoke.isSpecial()) {
                changed = callGraph.addEdge(new Edge<>(CallKind.SPECIAL,csCallSite,csMethod));
            }

            if(changed){
                addReachable(csMethod);
                InvokeExp invokeExp = invoke.getInvokeExp(); // get the invoke expression
                for(int i = 0; i < invokeExp.getArgCount(); i++) {
                    CSVar actual_i = csManager.getCSVar(recv.getContext(),invokeExp.getArg(i));
                    CSVar formal_i = csManager.getCSVar(c_t,callee.getIR().getParam(i));
                    addPFGEdge(actual_i,formal_i);
                    taintAnalysis.addTFGEdge(actual_i,formal_i);
                }
                if(invoke.getLValue()!=null){ // there is an x
                    for(Var returnVar : callee.getIR().getReturnVars()){
                        CSVar return_i = csManager.getCSVar(c_t,returnVar);
                        CSVar x = csManager.getCSVar(recv.getContext(),invoke.getLValue());
                        addPFGEdge(return_i,x);
                        taintAnalysis.addTFGEdge(return_i,x);
                    }
                }

                // taint specific rules
                // r = x.k(...) may generates a taint object
                if(taintAnalysis.isSource(callee) && invoke.getLValue()!=null){
                    CSVar csVar = csManager.getCSVar(c_t,invoke.getLValue()); // c:r
                    Obj obj = taintAnalysis.makeTaint(invoke,callee.getReturnType()); // t
                    Context heapContext = taintAnalysis.getEmptyContext(); // c of t, which is empty here
                    CSObj csObj = csManager.getCSObj(heapContext,obj); // c:t
                    PointsToSet pointsToSet = PointsToSetFactory.make(csObj); // {c:t}
                    workList.addEntry(csVar, pointsToSet);
                }
                // the callee may have a match in set TaintTransfer(<m,from,to,u>)
                // in this case, need to addTFGEdge
                taintAnalysis.TaintTransfer(invoke,callee,recv, recv.getContext());
                // the last parameter above is supposed to provide the context info at callsite
                // c_t (selected before) refers to the context info we choose for the callee
                // this causes 3/29 taint flows undetected
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }

    // make it possible for TaintAnalysiss to use
    public void addEntryToWorkList(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }
}
