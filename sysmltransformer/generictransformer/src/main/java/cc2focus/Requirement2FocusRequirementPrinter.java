package cc2focus;

import de.monticore.lang.componentconnector._symboltable.RequirementSymbol;
import de.monticore.lang.componentconnector._visitor.ComponentConnectorVisitor2;
import de.monticore.prettyprint.IndentPrinter;
import trafos.IExpressionPrinter;

public class Requirement2FocusRequirementPrinter
    implements ComponentConnectorVisitor2 {

  private final IndentPrinter printer;
  private final IExpressionPrinter expressionPrinter;

  public Requirement2FocusRequirementPrinter(IndentPrinter printer,
                                             IExpressionPrinter expressionPrinter,
                                             Boolean printComments) {
    super();
    this.printer = printer;
    this.expressionPrinter = expressionPrinter;
  }

  public String getContent() {
    return printer.getContent();
  }

  @Override
  public void visit(RequirementSymbol node) {
    if(node.isStateInvariant()) {
      printer.print("invariant ");
    }
    printer.println("requirement " + node.getName() + " {");
    printer.indent();

    printer.println("theory undefined;");

    printer.println("subject " + node.getSubject().getName() + ";");

    printer.print("assumptions ");
    for (int i = 0; i < node.getAssumptionsList().size(); i++) {
      printer.print("\"");
      var printedAssm = expressionPrinter.print(node.getAssumptions(i));
      printedAssm = printedAssm.replace("\\", "\\\\");
      printer.print(printedAssm);
      printer.print("\"");
    }
    printer.println(";");

    printer.print("guarantee \"");
    var printedGuar = expressionPrinter.print(node.getGuarantee());
    printedGuar = printedGuar.replace("\\", "\\\\");
    printer.print(printedGuar);
    printer.println("\";");

    printer.unindent();
    printer.print("}");
  }
}
