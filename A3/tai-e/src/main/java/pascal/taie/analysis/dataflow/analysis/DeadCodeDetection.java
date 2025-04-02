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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;
import pascal.taie.util.collection.Pair;

import java.util.*;

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

        deadCode.addAll(getUnReachableStmts(cfg, constants));
        deadCode.addAll(getDeadAssignments(cfg, liveVars));

        deadCode.remove(cfg.getEntry());
        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    // 遍历 CFG，把能遍历到的都加入到 visited，剩下的就是遍历不到的
    private static void controlFlowUnReachable(CFG<Stmt> cfg, Set<Stmt> visited, Stmt current) {
        if (visited.contains(current)) {
            return;
        } else {
            visited.add(current);
        }
        for (Stmt succ: cfg.getSuccsOf(current)) {
            controlFlowUnReachable(cfg, visited, succ);
        }
    }

    private static void ifBranchUnReachable(CFG<Stmt> cfg, Set<Stmt> visited, Stmt current, DataflowResult<Stmt, CPFact> constants) {
        if (visited.contains(current)) {
            return;
        } else {
            visited.add(current);
        }

        boolean flag = true;
        if (current instanceof If ifStmt) {
            ConditionExp condition = ifStmt.getCondition();
            Value conVal = ConstantPropagation.evaluate(condition, constants.getInFact(ifStmt));
            if (conVal.isConstant()) {
                int constantCondition = conVal.getConstant();
                // constantCondition = 1 -> true branch;
                // constantCondition = 0 -> false branch
                Set<Edge<Stmt>> outEdges = cfg.getOutEdgesOf(ifStmt);
                for (Edge<Stmt> outEdge: outEdges) {
                    if (outEdge.getKind() == Edge.Kind.IF_TRUE) {
                        if (constantCondition != 0) {
                            flag = false;
                            ifBranchUnReachable(cfg, visited, outEdge.getTarget(), constants);
                            break;
                        }
                    } else if (outEdge.getKind() == Edge.Kind.IF_FALSE) {
                        if (constantCondition == 0) {
                            flag = false;
                            ifBranchUnReachable(cfg, visited, outEdge.getTarget(), constants);
                            break;
                        }
                    }
                }
            }
        }
        if (flag) {
            for (Stmt succ: cfg.getSuccsOf(current)) {
                ifBranchUnReachable(cfg, visited, succ, constants);
            }
        }
    }

    private static void switchBranchUnReachable(CFG<Stmt> cfg, Set<Stmt> visited, Stmt current, DataflowResult<Stmt, CPFact> constants) {
        if (visited.contains(current)) {
            return;
        } else {
            visited.add(current);
        }

        boolean flag = true;
        if (current instanceof SwitchStmt switchStmt) {
            Var switchVar = switchStmt.getVar();
            Value switchVal = ConstantPropagation.evaluate(switchVar, constants.getInFact(switchStmt));
            if (switchVal.isConstant()) {
                int constantCondition = switchVal.getConstant();  // 只有 constantCondition 这个分支会被执行
                boolean found = false;
                for (Pair<Integer, Stmt> caseTarget: switchStmt.getCaseTargets()) {
                    if (caseTarget.first()==constantCondition) {
                        found = true;
                        switchBranchUnReachable(cfg, visited, caseTarget.second(), constants);
                        flag = false;
                    }
                }
                if (!found) {
                    switchBranchUnReachable(cfg, visited, switchStmt.getDefaultTarget(), constants);
                    flag = false;
                }
            }
        }
        if (flag) {
            for (Stmt succ: cfg.getSuccsOf(current)) {
                switchBranchUnReachable(cfg, visited, succ, constants);
            }
        }
    }

    private static Set<Stmt> getUnReachableStmts(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set <Stmt> allStmt = cfg.getNodes();
        Set <Stmt> visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set <Stmt> deadCodeStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        controlFlowUnReachable(cfg, visitedStmt, cfg.getEntry());
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        ifBranchUnReachable(cfg, visitedStmt, cfg.getEntry(), constants);
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        switchBranchUnReachable(cfg, visitedStmt, cfg.getEntry(), constants);
        updateDeadCode(allStmt, visitedStmt, deadCodeStmt);
        visitedStmt.clear();

        return deadCodeStmt;
    }

    private static void updateDeadCode(Set <Stmt> allStmt, Set <Stmt> visitedStmt, Set<Stmt> deadCodeStmt) {
        for (Stmt stmt: allStmt) {
            if (!visitedStmt.contains(stmt)) {
                deadCodeStmt.add(stmt);
            }
        }
    }

    private static void deadAssignment(CFG<Stmt> cfg, Set<Stmt> visited, Stmt current, Set<Stmt> deadCode,
                                       DataflowResult<Stmt, SetFact<Var>> liveVars) {
        if (visited.contains(current)) {
            return;
        } else {
            visited.add(current);
        }

        if (current instanceof AssignStmt assignStmt && hasNoSideEffect(assignStmt.getRValue())) {
            LValue lValue = assignStmt.getLValue();
            if (lValue instanceof Var var && !liveVars.getOutFact(assignStmt).contains(var)) {
                deadCode.add(current);
            }
        }

        for (Stmt succ: cfg.getSuccsOf(current)) {
            deadAssignment(cfg, visited, succ, deadCode, liveVars);
        }
    }

    private static Set<Stmt> getDeadAssignments(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set <Stmt> visitedStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Set <Stmt> deadCodeStmt = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        deadAssignment(cfg, visitedStmt, cfg.getEntry(), deadCodeStmt, liveVars);
        return deadCodeStmt;
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
