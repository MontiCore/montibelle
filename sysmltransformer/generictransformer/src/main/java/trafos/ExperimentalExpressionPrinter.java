package trafos;

import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression;
import de.monticore.expressions.expressionsbasis._visitor.ExpressionsBasisVisitor2;
import de.monticore.prettyprint.IndentPrinter;
import de.monticore.visitor.ITraverser;
import de.se_rwth.commons.logging.Log;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.IFocusScope;
import montibelle.focus._visitor.FocusTraverser;

import java.util.Set;

public class ExperimentalExpressionPrinter {

  private ITraverser traverser;

  private IndentPrinter printer;

  public ExperimentalExpressionPrinter(
      ITraverser traverser,
      IndentPrinter printer
  ) {
    this.traverser = traverser;
    this.printer = printer;
  }

  public ExperimentalExpressionPrinter() {
    FocusTraverser traverser = FocusMill.traverser();
    this.traverser = traverser;
    this.printer = new IndentPrinter();
    traverser.add4ExpressionsBasis(new ExpressionBasis2Isabelle(printer));
  }

  public String print(ASTExpression expression) {
    expression.accept(traverser);
    return printer.getContent();
  }

  public class ExpressionBasis2Isabelle implements ExpressionsBasisVisitor2 {
    private IndentPrinter printer;

    public ExpressionBasis2Isabelle(IndentPrinter printer) {
      this.printer = printer;
    }

    @Override
    public void visit(ASTNameExpression node) {
      var optChannel = getEnclosingScope(node).resolveChannel(node.getName());
      if(optChannel.isPresent()) {
        printer.print(optChannel.get().getPattern());
      }
      else {
        Log.warn("0xMPf702 Unrecognized name", node.get_SourcePositionStart(), node.get_SourcePositionEnd());
      }
    }

    protected IFocusScope getEnclosingScope(ASTExpression node) {
      if(node.getEnclosingScope() instanceof IFocusScope) {
        return (IFocusScope) node.getEnclosingScope();
      }
      else {
        Log.error("0xMPf701 Unexpected enclosing scope", node.get_SourcePositionEnd(), node.get_SourcePositionEnd());
        return null;
      }
    }
  }

}
