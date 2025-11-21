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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact boundaryFact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var param : params) {
            // Only track integer like variables.
            if (canHoldInt(param)) {
                boundaryFact.update(param, Value.getNAC());
            }
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        // Initially, all variable is UNDEF, which is absent in fact.
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // If fact does not have some keys of target, then these variables
        // are UNDEF, which can be safely ignored
        fact.forEach((variable, value) -> {
            Value targetValue = target.get(variable);
            target.update(variable, meetValue(value, targetValue));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isUndef()) {
            // UNDEF ⊓ v = v
            return v2;
        } else if (v2.isUndef()) {
            return v1;
        } else if (v1.isNAC() || v2.isNAC()) {
            // NAC ⊓ v = NAC
            return Value.getNAC();
        } else if (v1.equals(v2)) {
            // c ⊓ c = c
            return v1;
        } else {
            // c1 ⊓ c2 = NAC
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        if (!(stmt instanceof DefinitionStmt<?, ?>)) {
            return out.copyFrom(in);
        }
        Optional<LValue> def = stmt.getDef();
        if (def.isEmpty()) {
            return out.copyFrom(in);
        }
        LValue lValue = def.get();
        if (lValue instanceof Var x) {
            if (canHoldInt(x)) {
                Exp exp = ((DefinitionStmt<?, ?>) stmt).getRValue();
                CPFact copyIn = in.copy();
                Value gen = evaluate(exp, in);
                copyIn.update(x, gen);
                return out.copyFrom(copyIn);
            }
        }
        // uncovered cases such as o.f = e, identity transfer.
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var y) {
            return in.get(y);
        } else if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            Value opVal1 = in.get(operand1);
            Value opVal2 = in.get(operand2);
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            if (!canHoldInt(operand1) || !canHoldInt(operand2)) {
                return Value.getUndef();
            } else if (opVal2.isConstant() && opVal2.getConstant() == 0
                    // Easy to neglect the case a / 0, where a is UNDEF.
                    // Here we do a special judgement.
                    && (op.toString().equals("/") || op.toString().equals("%"))) {
                return Value.getUndef();
            } else if (opVal1.isConstant() && opVal2.isConstant()) {
                int value1 = opVal1.getConstant();
                int value2 = opVal2.getConstant();
                return switch (op.toString()) {
                    case "+" -> Value.makeConstant(value1 + value2);
                    case "-" -> Value.makeConstant(value1 - value2);
                    case "*" -> Value.makeConstant(value1 * value2);
                    case "/" -> Value.makeConstant(value1 / value2);
                    case "%" -> Value.makeConstant(value1 % value2);
                    case "==" -> Value.makeConstant(value1 == value2 ? 1 : 0);
                    case "!=" -> Value.makeConstant(value1 != value2 ? 1 : 0);
                    case "<" -> Value.makeConstant(value1 < value2 ? 1 : 0);
                    case ">" -> Value.makeConstant(value1 > value2 ? 1 : 0);
                    case "<=" -> Value.makeConstant(value1 <= value2 ? 1 : 0);
                    case ">=" -> Value.makeConstant(value1 >= value2 ? 1 : 0);
                    case "<<" -> Value.makeConstant(value1 << value2);
                    case ">>" -> Value.makeConstant(value1 >> value2);
                    case ">>>" -> Value.makeConstant(value1 >>> value2);
                    case "|" -> Value.makeConstant(value1 | value2);
                    case "&" -> Value.makeConstant(value1 & value2);
                    case "^" -> Value.makeConstant(value1 ^ value2);
                    default -> Value.getNAC();
                };
            } else if (in.get(operand1).isNAC() || in.get(operand2).isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        // Safe estimation.
        return Value.getNAC();
    }
}
