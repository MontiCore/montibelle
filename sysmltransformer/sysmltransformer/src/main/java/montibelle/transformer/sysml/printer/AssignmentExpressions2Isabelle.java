package montibelle.transformer.sysml.printer;

import de.monticore.expressions.assignmentexpressions._ast.ASTAssignmentExpression;
import de.monticore.expressions.assignmentexpressions._visitor.AssignmentExpressionsInheritanceHandler;
import de.monticore.expressions.assignmentexpressions._visitor.AssignmentExpressionsVisitor2;
import de.monticore.prettyprint.IndentPrinter;

public class AssignmentExpressions2Isabelle
    extends AssignmentExpressionsInheritanceHandler
    implements AssignmentExpressionsVisitor2 {

  protected final IndentPrinter printer;

  public AssignmentExpressions2Isabelle(IndentPrinter printer) {
    this.printer = printer;
  }

  @Override
  public void traverse(ASTAssignmentExpression node) {
    node.getLeft().accept(traverser);
    printer.print("=");
    node.getRight().accept(traverser);
  }
}
