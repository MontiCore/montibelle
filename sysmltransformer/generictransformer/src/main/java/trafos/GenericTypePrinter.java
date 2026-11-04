package trafos;

import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.check.SymTypeOfFunction;
import de.monticore.types.check.SymTypeOfGenerics;
import de.monticore.types.check.SymTypeOfObject;
import de.monticore.types.check.SymTypeOfTuple;
import de.monticore.types.check.SymTypePrimitive;

import java.util.Map;

public class GenericTypePrinter implements ITypePrinter {

  public static final Map<String, String> DEFAULT_BASIC_TYPES = Map.of(
      "boolean", "bool",
      "int", "int",
      "nat", "nat",
      "String", "string"
  );

  public static String getConstructorName(String typeName) {
    return typeName + "Constr";
  }

  private final Map<String, String> basicTypes;
  protected final ResettableIndentPrinter printer = new ResettableIndentPrinter();

  public GenericTypePrinter() {
    this.basicTypes = DEFAULT_BASIC_TYPES;
  }

  public GenericTypePrinter(Map<String, String> basicTypes) {
    this.basicTypes = basicTypes;
  }

  @Override
  public void visit(SymTypePrimitive primitive) {
    String mapped = basicTypes.get(primitive.print());
    printer.print(mapped != null ? mapped : primitive.print());
  }

  @Override
  public void visit(SymTypeOfGenerics generic) {
    switch (generic.getTypeInfo().getName()) {
      case "List":
        generic.getArgument(0).accept(this);
        printer.print(" list");
        break;

      case "Pair":
        generic.getArgument(0).accept(this);
        printer.print("\\<times>");
        generic.getArgument(1).accept(this);
        break;

      default:
        printer.print(generic.print());
        break;
    }
  }

  @Override
  public void visit(SymTypeOfObject objectType) {
    String mapped = basicTypes.get(objectType.print());
    printer.print(mapped != null ? mapped : objectType.print());
  }

  @Override
  public void visit(SymTypeOfTuple node) {
    printer.print("(");
    node.getType(0).accept(this);
    printer.print("\\<times>");
    node.getType(1).accept(this);
    printer.print(")");
  }

  @Override
  public void visit(SymTypeOfFunction node) {
    printer.print("(");
    for(var arg: node.getArgumentTypeList()) {
      arg.accept(this);
      printer.print("=>");
    }
    node.getType().accept(this);
    printer.print(")");
  }

  @Override
  public String print(SymTypeExpression typeExpression) {
    printer.reset();
    typeExpression.accept(this);
    return printer.getContent();
  }
}
