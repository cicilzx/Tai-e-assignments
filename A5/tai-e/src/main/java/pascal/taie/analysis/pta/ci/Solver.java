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
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

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
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            List<Stmt> stmts = method.getIR().getStmts();
            for (Stmt stmt : stmts) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Pointer ptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            workList.addEntry(ptr, new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer ptrLVar = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Pointer ptrRVar = pointerFlowGraph.getVarPtr(stmt.getRValue());
            pointerFlowGraph.addEdge(ptrRVar, ptrLVar);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                processSingleCall(stmt, callee);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Pointer ptrLVar = pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer ptrRVar = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                pointerFlowGraph.addEdge(ptrRVar, ptrLVar);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Pointer ptrLVar = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                Pointer ptrRVar = pointerFlowGraph.getVarPtr(stmt.getRValue());
                pointerFlowGraph.addEdge(ptrRVar, ptrLVar);
            }
            return null;
        }
    }


    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }


    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet pts = entry.pointsToSet();
            Pointer ptr = entry.pointer();
            PointsToSet delta = propagate(ptr, pts);
            if (ptr instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    // Store Field
                    List<StoreField> storeFieldStmts = var.getStoreFields();
                    for (StoreField storeField : storeFieldStmts) {
                        Pointer ptrLVar = pointerFlowGraph.getInstanceField(obj, storeField.getFieldAccess().getFieldRef().resolve());
                        Pointer ptrRVar = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }
                    // Load Field
                    List<LoadField> loadFieldStmts = var.getLoadFields();
                    for (LoadField loadField : loadFieldStmts) {
                        Pointer ptrLVar = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        Pointer ptrRVar = pointerFlowGraph.getInstanceField(obj, loadField.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }
                    // Store Array
                    List<StoreArray> storeArrayStmts = var.getStoreArrays();
                    for (StoreArray storeArray : storeArrayStmts) {
                        Pointer ptrLVar = pointerFlowGraph.getArrayIndex(obj);
                        Pointer ptrRVar = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }
                    // Load Array
                    List<LoadArray> loadArrayStmts = var.getLoadArrays();
                    for (LoadArray loadArray : loadArrayStmts) {
                        Pointer ptrLVar = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        Pointer ptrRVar = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(ptrRVar, ptrLVar);
                    }
                    // Process Call
                    processCall(var, obj);
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
        PointsToSet delta = new PointsToSet();
        for (Obj obj: pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Obj obj: delta) {
                pointer.getPointsToSet().addObject(obj);
            }
            Set<Pointer> succs = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer succ: succs) {
                workList.addEntry(succ, delta);
            }
        }
        return delta;
    }

    private void processSingleCall(Invoke callSite, JMethod callee) {
        if (!callGraph.getCalleesOf(callSite).contains(callee)) {
            CallKind kind = null;
            if (callSite.isInterface()) kind = CallKind.INTERFACE;
            else if (callSite.isStatic()) kind = CallKind.STATIC;
            else if (callSite.isSpecial()) kind = CallKind.SPECIAL;
            else if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
            else if (callSite.isDynamic()) kind = CallKind.DYNAMIC;
            if (kind != null) {
                callGraph.addEdge(new Edge<>(kind, callSite,callee));
                addReachable(callee);
                List<Var> args = callee.getIR().getParams();
                if (args.size() == callSite.getRValue().getArgs().size()) {
                    for (int i = 0; i < args.size(); i++) {
                        Pointer argPtr = pointerFlowGraph.getVarPtr(callSite.getRValue().getArgs().get(i));
                        Pointer paraPtr = pointerFlowGraph.getVarPtr(args.get(i));
                        addPFGEdge(argPtr, paraPtr);
                    }
                    if (callSite.getLValue() != null) {
                        List<Var> returnVars = callee.getIR().getReturnVars();
                        for (Var var: returnVars) {
                            Pointer varPtr = pointerFlowGraph.getVarPtr(var);
                            Pointer ptrLVar = pointerFlowGraph.getVarPtr(callSite.getLValue());
                            addPFGEdge(varPtr, ptrLVar);
                        }
                    }
                }
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        List<Invoke> callSites = var.getInvokes();
        for (Invoke callSite: callSites) {
            JMethod callee = resolveCallee(recv, callSite);
            VarPtr thisPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            workList.addEntry(thisPtr, new PointsToSet(recv));
            processSingleCall(callSite, callee);
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
