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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> worklist = new ArrayDeque<>();

        callGraph.addReachableMethod(entry);
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();

            for(Invoke callSite : callGraph.callSitesIn(method).toList()){
                Set<JMethod> callees = resolve(callSite);
                for(JMethod callee : callees){
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite),callSite,callee));
                    if(!callGraph.contains(callee)){
                        callGraph.addReachableMethod(callee);
                        worklist.add(callee);
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature subsignature = methodRef.getSubsignature();

        // static call
        if(callSite.isStatic()){
            JMethod m = methodRef.getDeclaringClass().getDeclaredMethod(subsignature);
            if(m != null){
                T.add(m);
            }
            return T;
        }

        // special call
        if(callSite.isSpecial()){
            JClass cm = methodRef.getDeclaringClass();
            if(cm != null){
                JMethod m = dispatch(cm, subsignature);
                if(m != null){
                    T.add(m);
                }
            }
            return T;
        }

        // virtual call
        // invoke_virtual and invoke_interface
        if(callSite.isVirtual() || callSite.isInterface()){
            // declared type of receiver variable at cs
            JClass c = methodRef.getDeclaringClass();
            if(c != null){
                Set<JClass> possible_type_of_the_receiver_object = getAllSubClasses_SelfIncluded(c);
                for(JClass jClass : possible_type_of_the_receiver_object){
                    JMethod m = dispatch(jClass, subsignature);
                    if(m != null){
                        T.add(m);
                    }
                }
            }
            return T;
        }

        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod m = jclass.getDeclaredMethod(subsignature);
        if(m != null && !m.isAbstract()){
            return m;
        }
        else{
            JClass superclass = jclass.getSuperClass();
            if(superclass != null){
                return dispatch(superclass, subsignature);
            }
        }
        return null;
    }

    // get all subclasses (not just direct subs) and self included
    // bfs
    private Set<JClass> getAllSubClasses_SelfIncluded(JClass root) {
        Set<JClass> result = new HashSet<>();
        Queue<JClass> worklist = new ArrayDeque<>();
        worklist.add(root);
        result.add(root);
        while(!worklist.isEmpty()){
            JClass cur = worklist.poll();
            Collection<JClass> directsubs = new ArrayList<>();
            // treat interface separately
            if(cur.isInterface()){
                directsubs.addAll(hierarchy.getDirectSubinterfacesOf(cur));
                directsubs.addAll(hierarchy.getDirectImplementorsOf(cur));
            }
            else{
                directsubs.addAll(hierarchy.getDirectSubclassesOf(cur));
            }
            for(JClass directsub : directsubs){
                if(!result.contains(directsub)){
                    result.add(directsub);
                    worklist.add(directsub);
                }
            }
        }
        return result;
    }
}
