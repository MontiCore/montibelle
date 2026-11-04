package montibelle.transformer.util;

import de.monticore.lang.sysmlparts.symboltable.adapters.EnumDef2TypeSymbolAdapter;
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol;
import de.monticore.types.check.SymTypeArray;
import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.check.SymTypeOfFunction;
import de.monticore.types.check.SymTypeOfGenerics;
import de.monticore.types.check.SymTypeOfObject;
import de.monticore.types.check.SymTypeOfTuple;
import de.monticore.types.check.SymTypePrimitive;
import de.monticore.types3.ISymTypeVisitor;
import montibelle.transformer.generic.Constants;

public class CountabilityVisitor implements ISymTypeVisitor {
  protected boolean result = false;

  public boolean getResult() {
    return result;
  }

  public void reset() {
    this.result = false;
  }

  @Override
  public void visit(SymTypeArray array) {
    array.getArgument().accept(this);
  }

  @Override
  public void visit(SymTypeOfGenerics generic) {
    if(!generic.getTypeInfo().getFullName().equals("List")) {
      result = false;
      return;
    }
    for (SymTypeExpression expr : generic.getArgumentList()) {
      expr.accept(this);
      if(!result) {
        return;
      }
    }
    result = true;
  }

  @Override
  public void visit(SymTypeOfObject object) {
    if(!object.hasTypeInfo()) {
      result = false;
      return;
    }
    if(object.getTypeInfo().getVariableList().isEmpty()) {
      result = true;
      return;
    }
    for (VariableSymbol v : object.getTypeInfo().getVariableList()) {
      v.getType().accept(this);
      if(!result) {
        return;
      }
    }
  }

  @Override
  public void visit(SymTypeOfTuple tuple) {
    for (SymTypeExpression expr : tuple.getTypeList()) {
      expr.accept(this);
      if(!result) {
        return;
      }
    }
    result = true;
  }

  @Override
  public void visit(SymTypePrimitive primitive) {
    result = "nat".equals(primitive.getPrimitiveName()) ||
        "int".equals(primitive.getPrimitiveName()) ||
        "String".equals(primitive.getPrimitiveName()) ||
        "boolean".equals(primitive.getPrimitiveName()) ||
        "boolean \\<times> boolean".equals(primitive.getPrimitiveName());
  }

  @Override
  public void visit(SymTypeOfFunction function) {
    boolean finiteArguments = function.getArgumentTypeList().stream()
        .allMatch(Constants::isTypeFinite);
    boolean returnCountable = this.calculate(function.getType());

    result = finiteArguments && returnCountable;
  }

  public boolean calculate(SymTypeExpression symType) {
    reset();
    symType.accept(this);
    return getResult();
  }
}
