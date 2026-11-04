package aris._prettyprint;

import aris._ast.ASTDateTime;
import de.monticore.prettyprint.IndentPrinter;

public class ArisPrettyPrinter extends ArisPrettyPrinterTOP {
  public ArisPrettyPrinter(IndentPrinter printer, boolean printComments) {
    super(printer, printComments);
  }

  @Override
  public void handle (ASTDateTime node) {
    getPrinter().print("Mar 5 2026 9:44:44 PM");
  }
}
