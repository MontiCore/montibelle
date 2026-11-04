package trafos;

import de.monticore.types.check.SymTypeExpression;
import de.monticore.types3.ISymTypeVisitor;

public interface ITypePrinter extends ISymTypeVisitor {
  String print(SymTypeExpression typeExpression);
}
