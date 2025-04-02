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

import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;

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
        // TODO - finish me
        CPFact fact = new CPFact();
        for(Var var: cfg.getIR().getParams()) {
            fact.update(var, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((var, val) -> {
            target.update(var, meetValue(val, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant()) {
                return Value.makeConstant(v1.getConstant());
            } else {
                return Value.getNAC();
            }
        } else if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        } else if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        } else if (v2.isUndef() && v1.isConstant()) {
            return Value.makeConstant(v1.getConstant());
        }
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if(out.update(var, value)){
                changed.set(true);
            }
        }));

        if (stmt instanceof DefinitionStmt<?, ?> s) {
            if(s.getLValue() instanceof Var var && canHoldInt(var)) {
                CPFact inCopy = in.copy();
                Value removedVal = inCopy.get(var);
                inCopy.remove(var);
                Value newVal = evaluate(s.getRValue(), in);
                out.update(var, newVal);
                return !removedVal.equals(newVal) || changed.get();
            }
        }
        return changed.get();
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
        // TODO - finish me
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        }

        if (exp instanceof Var) {
            if (in.get((Var) exp).isConstant()) {
                return Value.makeConstant(in.get((Var) exp).getConstant());
            }
            return in.get((Var) exp);
        }

        if (exp instanceof BinaryExp) {
            Var v1 = ((BinaryExp) exp).getOperand1();
            Var v2 = ((BinaryExp) exp).getOperand2();

            if (exp instanceof ArithmeticExp && in.get(v2).isConstant()) {
                if ((((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.DIV) ||
                        (((ArithmeticExp) exp).getOperator() == ArithmeticExp.Op.REM)) {
                    if (in.get(v2).getConstant()==0) {
                        return Value.getUndef();
                    }
                }
            }

            if (in.get(v1).isConstant() && in.get(v2).isConstant()) {
                int c1 = in.get(v1).getConstant();
                int c2 = in.get(v2).getConstant();

                if (exp instanceof ArithmeticExp) {
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD: { return Value.makeConstant(c1 + c2); }
                        case SUB: { return Value.makeConstant(c1 - c2); }
                        case MUL: { return Value.makeConstant(c1 * c2); }
                        case DIV: {
                            if (c2 == 0) return Value.getUndef();
                            return Value.makeConstant(c1 / c2);
                        }
                        case REM: {
                            if (c2 == 0) return Value.getUndef();
                            return Value.makeConstant(c1 % c2);
                        }
                    }
                } else if (exp instanceof ConditionExp) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case GE -> { return Value.makeConstant(c1>=c2?1:0); }
                        case LE -> { return Value.makeConstant(c1<=c2?1:0); }
                        case LT -> { return Value.makeConstant(c1<c2?1:0); }
                        case EQ -> { return Value.makeConstant(c1==c2?1:0); }
                        case NE -> { return Value.makeConstant(c1!=c2?1:0); }
                        case GT -> { return Value.makeConstant(c1>c2?1:0); }
                    }
                } else if (exp instanceof ShiftExp) {
                    switch (((ShiftExp) exp).getOperator()) {
                        case SHL -> { return Value.makeConstant(c1<<1); }
                        case SHR -> { return Value.makeConstant(c1>>1); }
                        case USHR -> { return Value.makeConstant(c1>>>1); }
                    }
                } else if (exp instanceof BitwiseExp) {
                    switch (((BitwiseExp) exp).getOperator()) {
                        case AND -> { return Value.makeConstant(c1 & c2); }
                        case OR -> { return Value.makeConstant(c1 | c2); }
                        case XOR -> { return Value.makeConstant(c1 ^ c2); }
                    }
                }
            } else if (in.get(v1).isNAC() || in.get(v2).isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getUndef();
    }
}
