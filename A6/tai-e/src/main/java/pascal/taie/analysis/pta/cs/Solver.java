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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            List<Stmt> stmtList = csMethod.getMethod().getIR().getStmts();
            for (Stmt stmt : stmtList) {
                stmt.accept(new StmtProcessor(csMethod));
            }
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
        public Void visit(New stmt) {
            Pointer ptr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(ctx, obj));
            workList.addEntry(ptr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            Pointer ptrRVal = csManager.getCSVar(context, stmt.getRValue());
            Pointer ptrLVal = csManager.getCSVar(context, stmt.getLValue());
            addPFGEdge(ptrRVal, ptrLVal);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
                CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
                processSingleCall(csCallSite, csCallee);
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                StaticField staticField = csManager.getStaticField(stmt.getFieldRef().resolve());
                Pointer ptrLVal = csManager.getCSVar(context, stmt.getLValue());
                addPFGEdge(staticField, ptrLVal);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                StaticField staticField = csManager.getStaticField(stmt.getFieldRef().resolve());
                Pointer ptrRVal = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(ptrRVal, staticField);
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
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

            if (ptr instanceof CSVar csVar) {
                Context ctx = csVar.getContext();
                Var var = csVar.getVar();

                for (CSObj csObj: delta) {
                    List<StoreField> storeFieldList = var.getStoreFields();
                    for (StoreField storeField: storeFieldList) {
                        Pointer ptrLVar = csManager.getInstanceField(csObj, storeField.getFieldAccess().getFieldRef().resolve());
                        Pointer ptrRVar = csManager.getCSVar(ctx, storeField.getRValue());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }

                    List<LoadField> loadFieldList = var.getLoadFields();
                    for (LoadField loadField: loadFieldList) {
                        Pointer ptrLVar = csManager.getCSVar(ctx, loadField.getLValue());
                        Pointer ptrRVar = csManager.getInstanceField(csObj, loadField.getFieldAccess().getFieldRef().resolve());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }

                    List<StoreArray> storeArrayList = var.getStoreArrays();
                    for (StoreArray storeArray: storeArrayList) {
                        Pointer ptrLVar = csManager.getArrayIndex(csObj);
                        Pointer ptrRVar = csManager.getCSVar(ctx, storeArray.getRValue());
                        addPFGEdge(ptrRVar, ptrLVar);
                    }

                    List<LoadArray> loadArrayList = var.getLoadArrays();
                    for (LoadArray loadArray: loadArrayList) {
                        Pointer ptrLVar = csManager.getCSVar(ctx, loadArray.getLValue());
                        Pointer ptrRVar = csManager.getArrayIndex(csObj);
                        addPFGEdge(ptrRVar, ptrLVar);
                    }

                    processCall(csVar, csObj);
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
        for (CSObj csObj: pointsToSet) {
            if (!pointer.getPointsToSet().contains(csObj)) {
                delta.addObject(csObj);
            }
        }
        if (!delta.isEmpty()) {
            for (CSObj csObj: delta) {
                pointer.getPointsToSet().addObject(csObj);
            }
            Set<Pointer> succs = pointerFlowGraph.getSuccsOf(pointer);
            for (Pointer succ: succs) {
                workList.addEntry(succ, delta);
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
        List<Invoke> invokeList = recv.getVar().getInvokes();
        for (Invoke invoke: invokeList) {
            JMethod callee = resolveCallee(recvObj, invoke);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
            Pointer ptrThis = csManager.getCSVar(calleeContext, callee.getIR().getThis());
            workList.addEntry(ptrThis, PointsToSetFactory.make(recvObj));
            processSingleCall(csCallSite, csCallee);
        }
    }

    private void processSingleCall(CSCallSite csCallSite, CSMethod callee) {
        Invoke callSite = csCallSite.getCallSite();
        Context callerCtx = csCallSite.getContext();
        Context calleeCtx = callee.getContext();

        if (!callGraph.getCalleesOf(csCallSite).contains(callee)) {
            CallKind kind = null;
            if (callSite.isStatic())    kind = CallKind.STATIC;
            if (callSite.isInterface()) kind = CallKind.INTERFACE;
            if (callSite.isSpecial()) kind = CallKind.SPECIAL;
            if (callSite.isVirtual()) kind = CallKind.VIRTUAL;
            if (callSite.isDynamic()) kind = CallKind.DYNAMIC;

            if (kind != null) {
                callGraph.addEdge(new Edge<>(kind, csCallSite, callee));
                addReachable(callee);
                List<Var> args = callee.getMethod().getIR().getParams();
                assert args.size() == callSite.getRValue().getArgs().size();
                for (int i = 0; i < args.size(); i++) {
                    Pointer argPtr = csManager.getCSVar(callerCtx, callSite.getRValue().getArgs().get(i));
                    Pointer paraPtr = csManager.getCSVar(calleeCtx, args.get(i));
                    addPFGEdge(argPtr, paraPtr);
                }
                if (callSite.getLValue() != null) {
                    List<Var> returnVars = callee.getMethod().getIR().getReturnVars();
                    for (Var returnVar: returnVars) {
                        Pointer returnPtr = csManager.getCSVar(calleeCtx, returnVar);
                        Pointer ptrLVar = csManager.getCSVar(callerCtx, callSite.getLValue());
                        addPFGEdge(returnPtr, ptrLVar);
                    }
                }
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

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
