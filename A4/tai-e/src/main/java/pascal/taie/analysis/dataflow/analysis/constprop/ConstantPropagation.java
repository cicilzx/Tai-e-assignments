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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        for (Var key : fact.keySet()) {
            Value v = meetValue(fact.get(key), target.get(key));
            target.update(key, v);
        }
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
        boolean changed = false;
        if (!out.equals(in)) {
            changed = true;
            out.copyFrom(in);
        }

        if (stmt instanceof DefinitionStmt definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            RValue rValue = definitionStmt.getRValue();

            if (lValue instanceof Var var) {
                if (canHoldInt(var)) {
                    CPFact tmp = in.copy();
                    tmp.remove(var);
                    Value removedVal = in.get(var);
                    Value newVal = evaluate(rValue, in);
                    if (!removedVal.equals(newVal)) {
                        tmp.update(var, newVal);
                        out.copyFrom(tmp);
                        changed = true;
                    }
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
        if (exp instanceof Var var) {
            if (in.get(var).isConstant()) {
                return Value.makeConstant(in.get(var).getConstant());
            }
            return in.get(var);
        }
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof BinaryExp binaryExp) {
            Var var1 = binaryExp.getOperand1();
            Var var2 = binaryExp.getOperand2();
            if (exp instanceof ArithmeticExp arithmeticExp) {
                if (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV || arithmeticExp.getOperator() == ArithmeticExp.Op.REM) {
                    if (in.get(var2).isConstant() && in.get(var2).getConstant()==0) {
                        return Value.getUndef();
                    }
                }
            }
            if (in.get(var1).isConstant() && in.get(var2).isConstant()) {
                Value v1 = in.get(var1);
                Value v2 = in.get(var2);
                int c1 = v1.getConstant();
                int c2 = v2.getConstant();
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> {return Value.makeConstant(c1 + c2);}
                        case SUB -> {return Value.makeConstant(c1 - c2);}
                        case MUL -> {return Value.makeConstant(c1 * c2);}
                        case DIV -> {return Value.makeConstant(c1 / c2);}
                        case REM -> {return Value.makeConstant(c1 % c2);}
                    }
                }
                if (exp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> {return Value.makeConstant(c1==c2?1:0);}
                        case NE -> {return Value.makeConstant(c1!=c2?1:0);}
                        case LT -> {return Value.makeConstant(c1<c2?1:0);}
                        case GT -> {return Value.makeConstant(c1>c2?1:0);}
                        case LE -> {return Value.makeConstant(c1<=c2?1:0);}
                        case GE -> {return Value.makeConstant(c1>=c2?1:0);}
                    }
                }
                if (exp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> {return Value.makeConstant(c1<<c2);}
                        case SHR -> {return Value.makeConstant(c1>>c2);}
                        case USHR -> {return Value.makeConstant(c1>>>c2);}
                    }
                }
                if (exp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case OR -> {return Value.makeConstant(c1|c2);}
                        case AND -> {return Value.makeConstant(c1&c2);}
                        case XOR -> {return Value.makeConstant(c1^c2);}
                    }
                }
            } else if (in.get(var1).isNAC() || in.get(var2).isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        }
        return Value.getNAC();
    }
}
