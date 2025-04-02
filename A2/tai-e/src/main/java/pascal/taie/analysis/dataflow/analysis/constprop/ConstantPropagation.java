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
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

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
        for (Var var: cfg.getIR().getParams()) {
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
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
        fact.forEach(((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        }));
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
        } else if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        } else if (v2.isConstant() && v1.isUndef()) {
            return Value.makeConstant(v2.getConstant());
        }
        return Value.getUndef();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 首先，更新 out = in，只要 out 发生变化，那么一定代表有更新
        boolean changed = false;
        if (!out.equals(in)) {
            out.copyFrom(in);
            changed = true;
        }

        // 如果是definition stmt，就需要按照 transfer function 重新计算 out
        if (stmt instanceof DefinitionStmt s) {
            if(s.getLValue() instanceof Var var && canHoldInt(var)) {
                CPFact tmp = in.copy();
                tmp.remove(var);
                Value removedVal = in.get(var);
                Value gen = evaluate(s.getRValue(), in);
                tmp.update(var, gen);

                if (!removedVal.equals(gen)) {  // 只要删除的 val 和 更新的 val 不一样，那就代表有更新
                    out.copyFrom(tmp);
                    changed = true;
                }
            }
        }
        return changed;
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
            int value = ((IntLiteral) exp).getValue();
            return Value.makeConstant(value);
        } else if (exp instanceof Var var) {
            if (in.get(var).isConstant()) {
                return Value.makeConstant(in.get(var).getConstant());
            }
            return in.get(var);
        } else if (exp instanceof BinaryExp b) {
            Value value1 = evaluate(b.getOperand1(), in);
            Value value2 = evaluate(b.getOperand2(), in);

            if (value2.isConstant() && exp instanceof ArithmeticExp) {
                if (((ArithmeticExp) exp).getOperator().equals(ArithmeticExp.Op.DIV) || ((ArithmeticExp) exp).getOperator().equals(ArithmeticExp.Op.REM)) {
                    if (value2.getConstant()==0) {
                        return Value.getUndef();
                    }
                }
            }

            if (value1.isConstant() && value2.isConstant()) {  // value1 op value2
                int c1 = value1.getConstant();
                int c2 = value2.getConstant();

                if (exp instanceof ArithmeticExp) {  // + - * / %
                    switch (((ArithmeticExp) exp).getOperator()) {
                        case ADD -> {return Value.makeConstant(c1 + c2);}
                        case SUB -> {return Value.makeConstant(c1 - c2);}
                        case MUL -> {return Value.makeConstant(c1 * c2);}
                        case DIV -> {
                            if (c2 == 0) {return Value.getUndef();}
                            return Value.makeConstant(c1 / c2);
                        }
                        case REM -> {
                            if (c2 == 0) {return Value.getUndef();}
                            return Value.makeConstant(c1 % c2);
                        }
                    }
                }
                if (exp instanceof ConditionExp) {
                    switch (((ConditionExp) exp).getOperator()) {
                        case EQ -> {return Value.makeConstant(c1==c2?1:0);}
                        case NE -> {return Value.makeConstant(c1!=c2?1:0);}
                        case LT -> {return Value.makeConstant(c1<c2?1:0);}
                        case GT -> {return Value.makeConstant(c1>c2?1:0);}
                        case LE -> {return Value.makeConstant(c1<=c2?1:0);}
                        case GE -> {return Value.makeConstant(c1>=c2?1:0);}
                    }
                }
                if (exp instanceof ShiftExp) {
                    return switch (((ShiftExp) exp).getOperator()) {
                        case SHL -> Value.makeConstant(c1<<c2);
                        case SHR -> Value.makeConstant(c1>>c2);
                        case USHR -> Value.makeConstant(c1>>>c2);
                    };
                }
                if (exp instanceof BitwiseExp) {
                    return switch (((BitwiseExp) exp).getOperator()) {
                        case AND -> Value.makeConstant(c1&c2);
                        case OR -> Value.makeConstant(c1|c2);
                        case XOR -> Value.makeConstant(c1^c2);
                    };
                }

            } else if (value1.isNAC() || value2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
