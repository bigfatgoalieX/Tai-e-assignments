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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.Collection;
import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact newOut = in.copy();
        if(!newOut.equals(out)) {
            out.copyFrom(newOut);
            return true;
        }
        return false;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact res = out.copy();
        return res;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact res = out.copy();
        Invoke callSite = (Invoke) edge.getSource();
        Var resultVar = callSite.getResult();
        if(resultVar != null && ConstantPropagation.canHoldInt(resultVar)) {
            // kill the result variable
            res.remove(resultVar);
        }

        return res;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        //        JMethod callee = (JMethod) edge.getTarget();
        JMethod callee = edge.getCallee();
        IR calleeIR = callee.getIR();
        List<Var> formals = calleeIR.getParams();
        int cnt_formals = formals.size();

        CPFact boundary = cp.newInitialFact();

        Invoke callSite = (Invoke) edge.getSource();
        // List<Var> uses = callSite.getInvokeExp().getUses();
        // the line above cause bug (failed;pass testcase 1013/1065)
        // why getArgs() is fine though?
        List<Var> uses = callSite.getInvokeExp().getArgs();
        int cnt_args = uses.size();

        int k = Math.min(cnt_args, cnt_formals);
        for(int i = 0; i < k; i++) {
            Exp actualExp = uses.get(i);
            Value v = ConstantPropagation.evaluate(actualExp,callSiteOut);
            Var formal = formals.get(i);
            if(ConstantPropagation.canHoldInt(formal)) {
                boundary.update(formal, v);
            }
        }
        return boundary;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact ret = cp.newInitialFact();

        Collection<Var> returnVars = edge.getReturnVars();
        Value merged = Value.getUndef();
        for(Var r: returnVars) {
            Value v = returnOut.get(r);
            if(merged.isUndef()){
                merged = v;
            }
            else {
                merged = cp.meetValue(merged, v);
            }
        }
        if(merged.isUndef()) {
            return ret;
        }

        Invoke callSite = (Invoke) edge.getCallSite();
        Var resultVar = callSite.getResult();
        if(resultVar != null && ConstantPropagation.canHoldInt(resultVar)) {
            ret.update(resultVar, merged);
        }

        return ret;
    }
}
