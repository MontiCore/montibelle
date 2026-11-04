package cc2focus;

import de.monticore.lang.componentconnector._symboltable.MildSpecificationSymbol;
import montibelle.focus._ast.ASTSpecificationBuilder;
import trafos.IExpressionPrinter;

import java.util.stream.Collectors;

public class Specification2Sps {

  public static ASTSpecificationBuilder buildSpecificaton(MildSpecificationSymbol node, IExpressionPrinter printer) {
    var ass = node.getAssumptionsList().stream()
        .map(printer::print)
        .collect(Collectors.toList());

    var preds = node.getPredicatesList().stream()
        .map(printer::print)
        .collect(Collectors.toList());

    var builder = new ASTSpecificationBuilder()
        .setAssumptionsList(ass)
        .setPredicatesList(preds);

    return builder;
  }

}
