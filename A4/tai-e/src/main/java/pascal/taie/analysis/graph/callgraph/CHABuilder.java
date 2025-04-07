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
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import soot.util.ArraySet;
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

    private CallKind getCallKind(Invoke callSite) {
        if (callSite.isVirtual()) {
            return CallKind.VIRTUAL;
        } else if (callSite.isStatic()) {
            return CallKind.STATIC;
        } else if (callSite.isInterface()) {
            return CallKind.INTERFACE;
        } else if (callSite.isSpecial()) {
            return CallKind.SPECIAL;
        } else if (callSite.isDynamic()) {
            return CallKind.DYNAMIC;
        }
        return null;
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        LinkedList<JMethod> workList = new LinkedList<>();
        workList.add(entry);

        while (!workList.isEmpty()) {
            JMethod method = workList.removeFirst();
            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                for (Invoke callSite: callGraph.getCallSitesIn(method)) {
                    Set<JMethod> targets = resolve(callSite);
                    CallKind kind = getCallKind(callSite);
                    if (kind != null) {
                        for (JMethod target: targets) {
                            if (target != null) {
                                callGraph.addEdge(new Edge<>(kind, callSite, target));
                                workList.addAll(targets);
                            }
                        }
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
        Set<JMethod> methods = new HashSet<>();

        if (callSite.isStatic()) {
            MethodRef methodRef = callSite.getMethodRef();
            JMethod method = methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature());
            methods.add(method);
        } else if (callSite.isSpecial()) {
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            JMethod method = dispatch(jClass, callSite.getMethodRef().getSubsignature());
            if (method != null) {
                methods.add(method);
            }
        } else if (callSite.isInterface() || callSite.isVirtual()) {
            LinkedList<JClass> subClasses = new LinkedList<>();
            JClass jClass = callSite.getMethodRef().getDeclaringClass();
            subClasses.add(jClass);

            while (!subClasses.isEmpty()) {
                JClass subClass = subClasses.removeFirst();
                JMethod jmethod = dispatch(subClass, callSite.getMethodRef().getSubsignature());
                if (jmethod != null) {
                    methods.add(jmethod);
                }
                if (subClass.isInterface()) {
                    subClasses.addAll(hierarchy.getDirectImplementorsOf(subClass));
                    subClasses.addAll(hierarchy.getDirectSubinterfacesOf(subClass));
                } else {
                    subClasses.addAll(hierarchy.getDirectSubclassesOf(subClass));
                }
            }
        }
        return methods;
    }




    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod jMethod = jclass.getDeclaredMethod(subsignature);
        if (jMethod != null && !jMethod.isAbstract()) {
            return jMethod;
        } else {
            if (jclass.getSuperClass()!= null) {
                return dispatch(jclass.getSuperClass(), subsignature);
            }
            return null;
        }
    }
}
