package de.monticore.types3;

import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.types.check.SymTypeExpression;

public final class TypeCheck3Access {
  private TypeCheck3Access() {}

  public static TypeCheck3 currentDelegate() {
    return TypeCheck3.delegate;
  }

  public static SymTypeExpression typeOf(TypeCheck3 typecheck, ASTExpression expression) {
    return typecheck._typeOf(expression);
  }
}
