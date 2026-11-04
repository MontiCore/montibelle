package montibelle.transformer.sysml.printer;

import de.monticore.expressions.assignmentexpressions._ast.ASTAssignmentExpression;
import de.monticore.expressions.commonexpressions._ast.ASTBracketExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.lang.sysmlbasis._ast.ASTSysMLUsage;
import de.monticore.lang.sysmlexpressions._ast.ASTConditionalAndExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTConditionalAndExpression2;
import de.monticore.lang.sysmlexpressions._ast.ASTConditionalNotExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTConditionalOrExpression2;
import de.monticore.lang.sysmlexpressions._ast.ASTElementOfExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTInfinity;
import de.monticore.lang.sysmlexpressions._ast.ASTKerMLExtentExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSqsubsetEquationExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSubsetEquationExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSubsetExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSupersetEquationExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSupersetExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLBodyExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLFunctionOperationExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLInstantiation;
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLSequenceExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTTernaryExpression;
import de.monticore.lang.sysmlexpressions._visitor.SysMLExpressionsInheritanceHandler;
import de.monticore.lang.sysmlexpressions._visitor.SysMLExpressionsVisitor2;
import de.monticore.lang.sysmlparts._ast.ASTAttributeUsage;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2._ast.ASTAnonymousUsage;
import de.monticore.prettyprint.IndentPrinter;
import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedType;
import de.monticore.types.mccollectiontypes._ast.ASTMCGenericType;
import de.monticore.types.mccollectiontypes._ast.ASTMCListType;
import de.monticore.types3.TypeCheck3;
import de.se_rwth.commons.logging.Log;
import montibelle.transformer.sysml.Constants;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class SysMLExpressions2Isabelle extends
    SysMLExpressionsInheritanceHandler implements SysMLExpressionsVisitor2 {

  protected final IndentPrinter printer;
  protected final IsabellePrinterSettings settings;

  public SysMLExpressions2Isabelle(IndentPrinter printer) {
    this(printer, new IsabellePrinterSettings());
  }

  public SysMLExpressions2Isabelle(
      IndentPrinter printer,
      IsabellePrinterSettings settings) {
    this.printer = printer;
    this.settings = settings;
  }

  public IndentPrinter getPrinter() {
    return printer;
  }

  @Override
  public void visit(ASTInfinity node) {
    if(node.isNegative()) {
      printer.print("(-\\<infinity>)");
    }
    else {
      printer.print("\\<infinity>");
    }
  }

  @Override
  public void traverse(ASTSubsetEquationExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<subseteq>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTSqsubsetEquationExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<sqsubseteq>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTSubsetExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<subset>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTSupersetEquationExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<supseteq>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTSupersetExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<supset>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTElementOfExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print("\\<in>");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTConditionalAndExpression node) {
    node.getLeft().accept(getTraverser());
    printer.print(" \\<and> ");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTConditionalAndExpression2 node) {
    node.getLeft().accept(getTraverser());
    printer.print(" \\<and> ");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTConditionalOrExpression2 node) {
    node.getLeft().accept(getTraverser());
    printer.print(" \\<or> ");
    node.getRight().accept(getTraverser());
  }

  @Override
  public void traverse(ASTConditionalNotExpression node) {
    printer.print("\\<not>(");
    node.getExpression().accept(getTraverser());
    printer.print(")");
  }

  public static boolean printSequenceAsSet = false;

  @Override
  public void traverse(ASTTernaryExpression node) {
    printer.print("(if ");

    node.getCondition().accept(getTraverser());
    printer.print(" then ");

    node.getIf().accept(getTraverser());
    printer.print(" else ");

    node.getElse().accept(getTraverser());

    printer.print(")");
  }

  @Override
  public void traverse(ASTSysMLInstantiation node) {
    String typeName = SysMLv2Mill.prettyPrint(node.getMCType(), false).trim();

    boolean isList = node.getMCType() instanceof ASTMCListType ||
        (node.getMCType() instanceof ASTMCQualifiedType &&
            ((ASTMCQualifiedType) node.getMCType()).getMCQualifiedName().getBaseName().equals(
                "List"));

    if(isList) {
      node.getArguments().accept(getTraverser());
      return;
    }

    printer.print(typeName + "Constr");

    node.getArguments().getExpressionList().forEach(arg -> {
      printer.print(" ");

      if(arg instanceof ASTAssignmentExpression) {
        ((ASTAssignmentExpression) arg).getRight().accept(getTraverser());
      }
      else {
        arg.accept(getTraverser());
      }
    });
  }

  @Override
  public void traverse(ASTSysMLBodyExpression node) {
    printer.print("(\\<lambda>");

    List<ASTSysMLUsage> parameters = node.getSysMLElementList().stream()
        .filter(ASTSysMLUsage.class::isInstance)
        .map(ASTSysMLUsage.class::cast)
        .filter(it -> {
          de.monticore.umlmodifier._ast.ASTModifier modifier = it.getModifier();
          if(modifier instanceof de.monticore.lang.sysmlv2._ast.ASTModifier) {
            de.monticore.lang.sysmlv2._ast.ASTModifier sysMLModifier =
                (de.monticore.lang.sysmlv2._ast.ASTModifier) modifier;
            return sysMLModifier.isIn()
                || (!sysMLModifier.isOut() && !sysMLModifier.isReturn());
          }
          return true;
        })
        .filter(it -> (it instanceof ASTAnonymousUsage
            && ((ASTAnonymousUsage) it).isPresentName())
            || (it instanceof ASTAttributeUsage
            && ((ASTAttributeUsage) it).isPresentName()))
        .collect(Collectors.toList());

    for (ASTSysMLUsage parameter : parameters) {
      printer.print(" ");
      if(parameter instanceof ASTAnonymousUsage) {
        printer.print(((ASTAnonymousUsage) parameter).getName());
      }
      else {
        parameter.accept(getTraverser());
      }
    }

    printer.print(". ");
    node.getInner().accept(getTraverser());
    printer.print(")");
  }

  @Override
  public void traverse(ASTSysMLFunctionOperationExpression node) {
    String fqn = ProvisorischerCode.getQualifiedNameOfFunction(node);
    Optional<String> isaMethodName = CommonExpressions2Isabelle.mapToIsabelle(fqn);

    if(node.isPresentBody() && isaMethodName.isPresent()) {
      printer.print(isaMethodName.get());
      Optional<Integer> posContArg = CommonExpressions2Isabelle.getPositionOfContArg(fqn);
      if(posContArg.isPresent() && posContArg.get() > 1) {
        Log.error("0xA8101 Die FunctionOperationExpression " + fqn + " hat "
            + "eine BodyExpression und kann daher kein stetiges Argument an "
            + "einer Position >1 haben. posContArg=" + posContArg.get(),
            node.get_SourcePositionStart(),node.get_SourcePositionEnd());
      }
      if(posContArg.isPresent() && posContArg.get().equals(0)) {
        printer.print("\\<cdot>");
      }
      else{
        printer.print(" ");
      }
      if(CommonExpressions2Isabelle.hasInvertedArguments(fqn)){
        node.getBody().accept(getTraverser());
      }
      else{
        printPossibleSetExpression(node.getExpression());
      }
      if(posContArg.isPresent() && posContArg.get().equals(1)) {
        printer.print("\\<cdot>");
      }
      else{
        printer.print(" ");
      }
      if(CommonExpressions2Isabelle.hasInvertedArguments(fqn)){
        printPossibleSetExpression(node.getExpression());
      }
      else{
        node.getBody().accept(getTraverser());
      }
    }
    else if(isaMethodName.isPresent()){
      printer.print(isaMethodName.get());
      int oldContArgsPos = settings.contArgPos;
      settings.contArgPos = CommonExpressions2Isabelle.getPositionOfContArg(fqn).orElse(-1);

      if(CommonExpressions2Isabelle.hasInvertedArguments(fqn)){
        node.getArguments().accept(getTraverser());
        ExpressionsBasis2Isabelle.printSeparator(printer,node.getArguments().getExpressionList().size());
        printPossibleSetExpression(node.getExpression());
      }
      else{
        ExpressionsBasis2Isabelle.printSeparator(printer,0);
        printPossibleSetExpression(node.getExpression());
        settings.contArgPos = settings.contArgPos -1;
        node.getArguments().accept(getTraverser());
      }
      settings.contArgPos = oldContArgsPos;
    }
    else {
      super.traverse(node);
    }
  }

  @Override
  public void traverse(ASTKerMLExtentExpression node){
    printer.print("UNIV :: ");
    var type = node.getMCType();
    if(type instanceof ASTMCGenericType){
      var argType = ((ASTMCGenericType) type).getMCTypeArgument(0).getMCTypeOpt().get();
      String typeStr = ((ASTMCQualifiedType)argType).getMCQualifiedName().getBaseName();
      printer.print(Constants.BASIC_TYPES.get(typeStr));
      printer.print(" stream");
    }
    else{
      SymTypeExpression typeExpr = TypeCheck3.symTypeFromAST(type);
      printer.print(new TypePrinter().print(typeExpr));
    }

    printer.print(" set");
  }

  protected void printPossibleSetExpression(ASTExpression expression){
    boolean oldIsSequenceSet = printSequenceAsSet;
    if (!(expression instanceof ASTBracketExpression)
        || !(((ASTBracketExpression) expression).getExpression()
        instanceof ASTKerMLExtentExpression)) {
      printSequenceAsSet = true;
    }
    expression.accept(getTraverser());
    printSequenceAsSet = oldIsSequenceSet;
  }

  @Override
  public void traverse(ASTSysMLSequenceExpression node) {
    if(printSequenceAsSet) {
      printer.print("{");
    }
    else {
      printer.print("(");
    }

    int size = node.getExpressionList().size();
    for (int index = 0; index < size; index++) {
      node.getExpressionList().get(index).accept(getTraverser());
      if(index < size - 1) {
        printer.print(",");
      }
    }

    if(printSequenceAsSet) {
      printer.print("}");
    }
    else {
      printer.print(")");
    }
  }

  @Override
  public void visit(ASTSysMLInstantiation node) {
    if(node.getMCType() instanceof ASTMCListType
        || (node.getMCType() instanceof ASTMCQualifiedType
        && ((ASTMCQualifiedType) node.getMCType()).getMCQualifiedName().getBaseName()
        .equals("List"))) {
      printer.print("[");
      settings.isBracketBeforeArg=true;
    }
    else {
      printer.print("(");
    }
  }

  @Override
  public void endVisit(ASTSysMLInstantiation node) {
    if(node.getMCType() instanceof ASTMCListType
        || (node.getMCType() instanceof ASTMCQualifiedType
        && ((ASTMCQualifiedType) node.getMCType()).getMCQualifiedName().getBaseName()
        .equals("List"))) {
      printer.print("]");
    }
    else {
      printer.print(")");
    }
  }
}
