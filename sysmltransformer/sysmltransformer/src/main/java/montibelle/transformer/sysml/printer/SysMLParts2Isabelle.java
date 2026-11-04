package montibelle.transformer.sysml.printer;

import de.monticore.lang.sysmlexpressions._ast.*;
import de.monticore.lang.sysmlparts._ast.ASTAttributeUsage;
import de.monticore.lang.sysmlparts._visitor.SysMLPartsInheritanceHandler;
import de.monticore.lang.sysmlparts._visitor.SysMLPartsVisitor2;
import de.monticore.prettyprint.IndentPrinter;

public class SysMLParts2Isabelle
  extends SysMLPartsInheritanceHandler
  implements SysMLPartsVisitor2
{

  protected final IndentPrinter printer;

  public SysMLParts2Isabelle(IndentPrinter printer) {
    this.printer = printer;
  }

  @Override
  public void visit(ASTAttributeUsage node) {
    printer.print("var_" + node.getName());
  }
}
