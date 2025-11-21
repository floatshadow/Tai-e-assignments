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
        // control-flow unreachable code, pessimistic analysis.
        // first assume all nodes are unreachable, then try to prove live nodes are reachable.

        Set<Stmt> liveNodes = new HashSet<>();
        Queue<Stmt> worklist = new LinkedList<>();
        // entry and exit should be reachable
        worklist.add(cfg.getEntry());
        worklist.add(cfg.getExit());
        while (!worklist.isEmpty()) {
            Stmt node = worklist.remove();
            if (liveNodes.contains(node)) {
                continue;
            }
            // mark reachable
            liveNodes.add(node);
            // unreachable branch analysis
            if (node instanceof If) {
                ConditionExp cond = ((If) node).getCondition();
                Value condVal = ConstantPropagation.evaluate(cond, constants.getInFact(node));
                if (condVal.isConstant()) {
                    Set<Edge<Stmt>> edges = cfg.getOutEdgesOf(node);
                    // only false branch reachable.
                    if (condVal.getConstant() == 0) {
                        for (Edge<Stmt> edge : edges) {
                            if (edge.getKind() == Edge.Kind.IF_FALSE) {
                                worklist.add(edge.getTarget());
                            }
                        }
                    } else {
                        // only true branch is reachable
                        worklist.add(((If) node).getTarget());
                    }
                    continue;
                }
            } else if (node instanceof SwitchStmt) {
                Var condVar = ((SwitchStmt) node).getVar();
                Value condVal = ConstantPropagation.evaluate(condVar, constants.getInFact(node));
                if (condVal.isConstant()) {
                    int cond = condVal.getConstant();
                    boolean fallback = true;
                    for (Pair<Integer, Stmt> case_target : ((SwitchStmt) node).getCaseTargets()) {
                        Integer caseVal = case_target.first();
                        Stmt target = case_target.second();
                        if (caseVal.equals(cond)) {
                            worklist.add(target);
                            fallback = false;
                        }
                    }
                    // only default branch is reachable.
                    if (fallback) {
                        worklist.add(((SwitchStmt) node).getDefaultTarget());
                    }
                    continue;
                }
            } else if (node instanceof AssignStmt) {
                // check useless assignment
                LValue lvalue = ((AssignStmt<?, ?>) node).getLValue();
                RValue rvalue = ((AssignStmt<?, ?>) node).getRValue();
                if (lvalue instanceof Var x &&
                        !liveVars.getOutFact(node).contains(x) &&
                        hasNoSideEffect(rvalue)
                ) {
                    // reachable, but can be removed
                    deadCode.add(node);
                }
            }
            // conservative estimation
            worklist.addAll(cfg.getSuccsOf(node));
        }
        for (Stmt node : cfg.getNodes()) {
            if (!liveNodes.contains(node)) {
                deadCode.add(node);
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
