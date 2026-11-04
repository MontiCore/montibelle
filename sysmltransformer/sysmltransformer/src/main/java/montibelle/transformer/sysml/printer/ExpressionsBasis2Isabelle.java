package montibelle.transformer.sysml.printer;

import de.monticore.expressions.expressionsbasis._ast.ASTArguments;
import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression;
import de.monticore.expressions.expressionsbasis._visitor.ExpressionsBasisInheritanceHandler;
import de.monticore.expressions.expressionsbasis._visitor.ExpressionsBasisVisitor2;
import de.monticore.prettyprint.IndentPrinter;

import java.util.List;

import static montibelle.transformer.sysml.extensions.ASTNameExpressionKt.getIsabelleName;

public class ExpressionsBasis2Isabelle
    extends ExpressionsBasisInheritanceHandler
    implements ExpressionsBasisVisitor2 {

  protected final IndentPrinter printer;
  protected static IsabellePrinterSettings settings;

  public ExpressionsBasis2Isabelle(
      IndentPrinter printer,
      IsabellePrinterSettings settings) {
    this.printer = printer;
    ExpressionsBasis2Isabelle.settings = settings;
  }

  public ExpressionsBasis2Isabelle(IndentPrinter printer) {
    this.printer = printer;
    ExpressionsBasis2Isabelle.settings = new IsabellePrinterSettings();
  }

  @Override
  public void visit(ASTNameExpression node) {
    switch (node.getName()) {
      case "Pair":
        printer.print("(");
        break;
      case "List":
        printer.print("[");
        break;
      default:
        printer.print(getIsabelleName(node));
        break;
    }
  }

  @Override
  public void endVisit(ASTNameExpression node) {
    switch (node.getName()) {
      case "Pair":
        printer.print(")");
        break;
      case "List":
        printer.print("]");
        break;
    }
  }

  @Override
  public void traverse(ASTArguments node) {
    List<ASTExpression> arguments = node.getExpressionList();

    if (settings.isFirstArgPrintedLast) {
      for (int index = 1; index < arguments.size(); index++) {
        printSeparator(printer,index - 1);
        arguments.get(index).accept(getTraverser());
      }

      if (!arguments.isEmpty()) {
        printSeparator(printer,arguments.size() - 1);
        arguments.get(0).accept(getTraverser());
      }

      return;
    }
    for (int index = 0; index < arguments.size(); index++) {
      if(!settings.isBracketBeforeArg){
        printSeparator(printer,index);
      }
      arguments.get(index).accept(getTraverser());
    }
    settings.isBracketBeforeArg = false;
  }

  public static void printSeparator(IndentPrinter printer, int originalArgumentPosition) {
    if (settings.contArgPos == originalArgumentPosition) {
      printer.print("\\<cdot>");
    }
    else if (settings.weAreInAConstructor) {
      printer.print(", ");
    }
    else {
      printer.print(" ");
    }
  }
}

