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

package pascal.taie.analysis.pta.plugin.taint;

import com.google.common.collect.Sets;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.analysis.pta.core.heap.Obj;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final TaintFlowGraph taintFlowGraph;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
        taintFlowGraph = new TaintFlowGraph();
    }

    // TODO - finish me

    // implementation for the 3 TaintTransfer Rules
    // r = x.k(a1,...,an)
    // base -> result
    // arg -> base
    // arg -> result
    public void TaintTransfer(Invoke stmt, JMethod callee, CSVar recv, Context callsitecontext){
        // check whether the callee is in TaintTransfers(set of <m,from,to,u>)
        Set<TaintTransfer> m_matched =  Sets.newHashSet();
        for(TaintTransfer taintTransfer : config.getTransfers()){
            if(taintTransfer.method().getSubsignature().equals(callee.getSubsignature())){
                m_matched.add(taintTransfer);
            }
        }
        // nothing matches
        if(m_matched.isEmpty()){
            return;
        }
        for(TaintTransfer tt : m_matched){
            // base -> result
            if(tt.from() == -1 && tt.to() == -2 && recv != null && stmt.getLValue() != null){
                CSVar base = recv;
                CSVar result = csManager.getCSVar(callsitecontext,stmt.getLValue());
                addTFGEdge(base, result);
            }
            // arg -> base
            if(tt.from() >= 0 && tt.to() == -1 && recv != null ){
                CSVar arg = csManager.getCSVar(callsitecontext,stmt.getInvokeExp().getArg(tt.from()));
                CSVar base = recv;
                addTFGEdge(arg, base);
            }
            // arg -> result
            if(tt.from() >= 0 && tt.to() == -2 && stmt.getLValue() != null){
                CSVar arg = csManager.getCSVar(callsitecontext,stmt.getInvokeExp().getArg(tt.from()));
                CSVar result = csManager.getCSVar(callsitecontext,stmt.getLValue());
                addTFGEdge(arg, result);
            }
        }
    }

    public void addTFGEdge(Pointer source, Pointer target) {
        if(taintFlowGraph.addEdge(source, target)) {
            if(!source.getPointsToSet().isEmpty()) {
                PointsToSet setoftaintobj = PointsToSetFactory.make();
                for(CSObj csObj : source.getPointsToSet()) {
                    if(isTaint(csObj.getObject())){
                        setoftaintobj.addObject(csObj);
                    }
                }
                if(!setoftaintobj.isEmpty()) {
                    solver.addEntryToWorkList(target, setoftaintobj);
                }
            }
        }
    }

    // make it possible for Solver to use
    public boolean isTaint(Obj obj){
        return manager.isTaint(obj);
    }

    // return true if the given method is a taint source according to the input info
    public boolean isSource(JMethod method) {
        Source source = new Source(method,method.getReturnType());
        return config.getSources().contains(source);
    }

    public boolean isSink(JMethod method) {
        Set<JMethod> sinkMethods = new HashSet<>();
        for(Sink sink : config.getSinks()) {
            sinkMethods.add(sink.method());
        }
        return sinkMethods.contains(method);
    }

    //
    public Obj makeTaint(Invoke source, Type type) {
        return manager.makeTaint(source, type);
    }

    public Context getEmptyContext() {
        return emptyContext;
    }

    public Set<Pointer> getSuccsOf(Pointer pointer) {
        return taintFlowGraph.getSuccsOf(pointer);
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            JMethod callee = edge.getCallee().getMethod();
            if(isSink(callee)){
                for(Sink sink : config.getSinks()) {
                    // try to match sink
                    if(sink.method().getSubsignature().equals(callee.getSubsignature())){
                        Var var = edge.getCallSite().getCallSite().getInvokeExp().getArg(sink.index());
                        CSVar csVar = csManager.getCSVar(edge.getCallSite().getContext(),var);
                        for(CSObj csObj : result.getPointsToSet(csVar)) {
                            if(isTaint(csObj.getObject())){
                                Invoke sourceCall = manager.getSourceCall(csObj.getObject());
                                Invoke sinkCall = edge.getCallSite().getCallSite();
                                int index = sink.index();
                                taintFlows.add(new TaintFlow(sourceCall, sinkCall, index));
                            }
                        }
                    }
                }
            }
        });
        return taintFlows;
    }
}

class TaintFlowGraph {

    /**
     * Map from a taint (node) to its successors in TFG.
     */
    private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

    /**
     * Adds an edge (source -> target) to this TFG.
     *
     * @return true if this TFG changed as a result of the call,
     * otherwise false.
     */
    boolean addEdge(Pointer source, Pointer target) {
        return successors.put(source, target);
    }

    /**
     * @return successors of given pointer in the TFG.
     */
    Set<Pointer> getSuccsOf(Pointer pointer) {
        return successors.get(pointer);
    }
}
