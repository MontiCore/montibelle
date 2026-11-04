package focus;

import de.monticore.types.check.SymTypeArray;
import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.check.SymTypeOfFunction;
import de.monticore.types.check.SymTypeOfGenerics;
import de.monticore.types.check.SymTypeOfObject;
import de.monticore.types.check.SymTypeOfTuple;
import de.monticore.types.check.SymTypePrimitive;
import de.monticore.types.check.SymTypeVoid;
import trafos.ITypePrinter;
import trafos.ResettableIndentPrinter;

public class SymType2MCTypePrinter implements ITypePrinter {

  public SymType2MCTypePrinter() {}

  protected final ResettableIndentPrinter printer =
      new ResettableIndentPrinter();

  @Override
  public void visit(SymTypePrimitive primitive) {
    printer.print(primitive.getPrimitiveName());
  }

  @Override
  public void visit(SymTypeVoid type) {
    printer.print("void");
  }

  @Override
  public void visit(SymTypeOfObject object) {
    String name = object.printFullName();
    switch (name) {
      case "Boolean": printer.print("boolean"); break;
      case "ScalarValues.Boolean": printer.print("boolean"); break;
      case "Integer": printer.print("int"); break;
      case "ScalarValues.Integer": printer.print("int"); break;
      case "Natural": printer.print("nat"); break;
      case "ScalarValues.Natural": printer.print("nat"); break;
      case "String": printer.print("String"); break;
      case "ScalarValues.String": printer.print("String"); break;
      default: printer.print(name);
    };
  }

  @Override
  public void visit(SymTypeArray array) {
    printer.print("List<");
    array.getArgument().accept(this);
    printer.print(">");
  }

  @Override
  public void visit(SymTypeOfGenerics generics) {
    printer.print(generics.getTypeInfo().getFullName());
    printer.print("<");
    for (int i = 0; i < generics.sizeArguments(); i++) {
      if (i > 0) {
        printer.print(", ");
      }
      generics.getArgument(i).accept(this);
    }
    printer.print(">");
  }

  @Override
  public void visit(SymTypeOfFunction function) {
    printer.print("(");
    for (int i = 0; i < function.sizeArgumentTypes(); i++) {
      if (i > 0) {
        printer.print(", ");
      }
      var argument = function.getArgumentType(i);
      if (argument.isFunctionType()) {
        printer.print("(");
      }
      argument.accept(this);
      if (argument.isFunctionType()) {
        printer.print(")");
      }
      if (function.isElliptic() && i == function.sizeArgumentTypes() - 1) {
        printer.print("...");
      }
    }
    printer.print(") -> ");
    function.getType().accept(this);
  }

  @Override
  public void visit(SymTypeOfTuple tuple) {
    printer.print("(");
    for (int i = 0; i < tuple.sizeTypes(); i++) {
      if (i > 0) {
        printer.print(", ");
      }
      tuple.getType(i).accept(this);
    }
    printer.print(")");
  }

  public String print(SymTypeExpression expression) {
    if (expression == null) {
      throw new IllegalArgumentException(
          "Cannot print a null SymTypeExpression");
    }
    printer.reset();
    expression.accept(this);
    return printer.getContent();
  }
}
