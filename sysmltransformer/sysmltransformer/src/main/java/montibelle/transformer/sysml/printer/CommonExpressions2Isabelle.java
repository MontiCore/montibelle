package montibelle.transformer.sysml.printer;

import de.monticore.expressions.commonexpressions._ast.*;
import de.monticore.expressions.commonexpressions._visitor.CommonExpressionsInheritanceHandler;
import de.monticore.expressions.commonexpressions._visitor.CommonExpressionsVisitor2;
import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression;
import de.monticore.lang.sysmlparts._symboltable.ISysMLPartsScope;
import de.monticore.lang.sysmlparts._symboltable.PortUsageSymbol;
import de.monticore.lang.sysmlv2._symboltable.SysMLv2Scope;
import de.monticore.prettyprint.IndentPrinter;
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol;
import de.monticore.types3.TypeCheck3Access;
import montibelle.focus.FocusTool;
import montibelle.transformer.sysml.Constants;

import java.util.Optional;
import java.util.Set;

public class CommonExpressions2Isabelle
    extends CommonExpressionsInheritanceHandler
    implements CommonExpressionsVisitor2 {

  protected final IndentPrinter printer;
  protected final IsabellePrinterSettings settings;

  public CommonExpressions2Isabelle(IndentPrinter printer) {
    this(printer, new IsabellePrinterSettings());
  }

  public CommonExpressions2Isabelle(
      IndentPrinter printer,
      IsabellePrinterSettings settings) {
    this.printer = printer;
    this.settings = settings;
  }

  public IsabellePrinterSettings getSettings() {
    return settings;
  }

  @Override
  public void visit(ASTBracketExpression node) {
    printer.print("(");
  }

  @Override
  public void endVisit(ASTBracketExpression node) {
    printer.print(")");
  }

  @Override
  public void visit(ASTLogicalNotExpression node) {
    printer.print("(Not ");
  }

  @Override
  public void endVisit(ASTLogicalNotExpression node) {
    printer.print(")");
  }

  @Override
  public void visit(ASTInfixExpression node) {
    printer.print("(");
  }

  @Override
  public void traverse(ASTBooleanOrOpExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" \\<or> ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTBooleanAndOpExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" \\<and> ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTPlusExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" + ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTMinusExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" - ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTLessThanExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" < ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTLessEqualExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" <= ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTGreaterThanExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" > ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTGreaterEqualExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" >= ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTEqualsExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" = ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void traverse(ASTNotEqualsExpression node) {
    node.getLeft().accept(this.traverser);
    printer.print(" \\<noteq> ");
    node.getRight().accept(this.traverser);
  }

  @Override
  public void endVisit(ASTInfixExpression node) {
    printer.print(")");
  }

  @Override
  public void visit(ASTCallExpression node) {
    printer.print("(");
  }

  @Override
  public void traverse(ASTCallExpression node) {
    ASTExpression lhs = node.getExpression();
    String fqn = ProvisorischerCode.getQualifiedNameOfFunction(lhs);

    if(ProvisorischerCode.isStatic(fqn)) {
      printer.print(mapToIsabelle(fqn).get());
      int oldContArgsPos = settings.contArgPos;
      boolean oldFirstArgPrintedLast = settings.isFirstArgPrintedLast;
      settings.contArgPos = getPositionOfContArg(fqn).orElse(-1);
      settings.isFirstArgPrintedLast = hasInvertedArguments(fqn);
      node.getArguments().accept(traverser);
      settings.isFirstArgPrintedLast = oldFirstArgPrintedLast;
      settings.contArgPos = oldContArgsPos;

    }
    else {
      Optional<String> potInfix = mapToIsabelleInfix(fqn);
      if(potInfix.isPresent()) {
        node.getArguments().accept(traverser);
        printer.print(potInfix.get());
        lhs.accept(traverser);
      }
      else {
        Optional<String> isabelleFun = mapToIsabelle(fqn);
        if(isabelleFun.isPresent() && Set.of(
            "EventStream.times", "EventStream.nth", "UntimedStream.values",
            "EventStream.values").contains(fqn)) {
          printer.print(isabelleFun.get());
          int oldContArgsPos = settings.contArgPos;
          boolean oldFirstArgPrintedLast = settings.isFirstArgPrintedLast;
          settings.contArgPos = getPositionOfContArg(fqn).orElse(-1);
          settings.isFirstArgPrintedLast = hasInvertedArguments(fqn);
          node.getArguments().accept(traverser);
          ExpressionsBasis2Isabelle.printSeparator(printer,node.getArguments().getExpressionList().size());
          settings.isFirstArgPrintedLast = oldFirstArgPrintedLast;
          settings.contArgPos = oldContArgsPos;

          ProvisorischerCode.getObject(lhs).accept(traverser);
        }
        else {
          lhs.accept(traverser);
          node.getArguments().accept(traverser);
        }
      }
    }
  }

  @Override
  public void endVisit(ASTCallExpression node) {
    printer.print(")");
  }

  public static Optional<String> mapToIsabelle(String fqn) {
    switch (fqn) {
      case "Stream.len": return Optional.of("slen\\<cdot>");
      case "List.count": return Optional.of("length ");
      case "List.size": return Optional.of("Packet_get_size ");
      case "EventStream.untimed": return Optional.of("e2ustream\\<cdot>");
      case "List.head": return Optional.of("hd ");
      case "List.tail": return Optional.of("tl ");
      case "List.append": return Optional.of("append ");
      case "Stream.rcDups": return Optional.of("srcdups\\<cdot>");
      case "EventStream.nth": return Optional.of("esnth");
      case "EventStream.times": return Optional.of("sntimes");
      case "UntimedStream.values": return Optional.of("sValues");
      case "EventStream.values": return Optional.of("eValues");
      case "EventStream.eRcDups": return Optional.of("srcdups");
      case "EventStream.eInfTimes": return Optional.of("sinftimes");
      case "EventStream.eTimes": return Optional.of("sntimes");
      case "EventStream.eZip": return Optional.of("ezip\\<cdot>");
      case "EventStream.eProjSnd": return Optional.of("eprojSnd");
      case "EventStream.eProjFst": return Optional.of("eprojFst");
      case "EventStream.eDropWhile": return Optional.of("edropwhile");
      case "EventStream.eTakeWhile": return Optional.of("etakewhile");
      case "EventStream.eDropMultiple": return Optional.of("edropMsg");
      case "EventStream.eTake": return Optional.of("etakeMsg");
      case "EventStream.eFinerTime": return Optional.of("e2finerTime");
      case "EventStream.eRougherTime": return Optional.of("e2rougherTime");
      case "EventStream.first": return Optional.of("eshdts");
      case "EventStream.eNth": return Optional.of("esnth");
      case "SyncStream.map": return Optional.of("tsynMap");
      case "EventStream.eMap": return Optional.of("emap");
      case "EventStream.eUntimed": return Optional.of("e2ustream");
      case "EventStream.eFilter": return Optional.of("efilter");
      case "ToptStream.toptFilter": return Optional.of("tsynFilter2");
      case "ToptStream.toptDropMultiple": return Optional.of("sdrop");
      case "ToptStream.toptTake": return Optional.of("stake");
      case "ToptStream.toptRcDups": return Optional.of("srcdups");
      case "ToptStream.toptTimes": return Optional.of("sntimes");
      case "ToptStream.toptInfTimes": return Optional.of("sinftimes");
      case "ControlFunctions.select": return Optional.of("filter");
      case "ControlFunctions.exists": return Optional.of("Bex");
      case "ControlFunctions.forAll": return Optional.of("Ball");
      case "SyncStream.syncFilter": return Optional.of("toneFilter2");
      case "SyncStream.syncEvent": return Optional.of("tone2event");
      case "SyncStream.syncTopt": return Optional.of("tone2tsyn");
      case "SyncStream.syncUntimed": return Optional.of("tone2ustream");
      case "SyncStream.syncDropMultiple": return Optional.of("sdrop");
      case "SyncStream.syncTake": return Optional.of("stake");
      case "SyncStream.syncRcDups": return Optional.of("srcdups");
      case "SyncStream.syncInfTimes": return Optional.of("sinftimes");
      case "SyncStream.syncTimes": return Optional.of("sntimes");
      case "SyncStream.syncProjFst": return Optional.of("tsynProjFst");
      case "SyncStream.syncProjSnd": return Optional.of("tsynProjSnd");
      case "UntimedStream.uFilter": return Optional.of("sFilter2");
      case "UntimedStream.uDropMultiple": return Optional.of("sdrop");
      case "UntimedStream.uTake": return Optional.of("stake");
      case "UntimedStream.uProjFst": return Optional.of("sprojfst");
      case "UntimedStream.uProjSnd": return Optional.of("sprojsnd");
      case "VerificationLibrary.ReachableStates": return Optional.of("sreachableStates (behavior.eaut ())\\<cdot> ");
    }
    return Optional.empty();
  }

  public static Optional<String> mapToIsabelleInfix(String fqn) {
    switch (fqn) {
      case "SequenceFunctions.includes": return Optional.of(" \\<in> ");
      case "SequenceFunctions.excludes": return Optional.of(" \\<notin> ");
      case "SequenceFunctions.intersection": return Optional.of(" \\<inter> ");
      case "UntimedStream.setFilter": return Optional.of(" \\<ominus> ");
      default: return Optional.empty();
    }
  }

  public static Optional<Integer> getPositionOfContArg(String fqn) {
    switch(fqn){
      case "UntimedStream.uFilter":
      case "UntimedStream.uDropMultiple":
      case "UntimedStream.uTake":
      case "ToptStream.toptFilter":
      case "ToptStream.toptDropMultiple":
      case "ToptStream.toptTake":
      case "SyncStream.syncFilter":
      case "SyncStream.syncDropMultiple":
      case "SyncStream.syncTake":
      case "SyncStream.map":
      case "EventStream.eZip":
      case "EventStream.eDropWhile":
      case "EventStream.eTakeWhile":
      case "EventStream.eDropMultiple":
      case "EventStream.eTake":
      case "EventStream.eRougherTime":
      case "EventStream.eFilter":
      case "EventStream.eMap":
      case "EventStream.nth":
      case "EventStream.eNth": return Optional.of(1);
      case "Stream.rcDups":
      case "UntimedStream.uProjFst":
      case "UntimedStream.uProjSnd":
      case "UntimedStream.values":
      case "EventStream.eRcDups":
      case "EventStream.eProjSnd":
      case "EventStream.eProjFst":
      case "EventStream.first":
      case "EventStream.eUntimed":
      case "EventStream.values":
      case "ToptStream.toptRcDups":
      case "SyncStream.syncEvent":
      case "SyncStream.syncTopt":
      case "SyncStream.syncUntimed":
      case "SyncStream.syncRcDups":
      case "SyncStream.syncProjFst":
      case "SyncStream.syncProjSnd": return Optional.of(0);
      default: return Optional.empty();
    }
  }

  public static boolean hasInvertedArguments(String fqn) {
    switch (fqn) {
      case "UntimedStream.uFilter":
      case "UntimedStream.uDropMultiple":
      case "UntimedStream.uTake":
      case "SyncStream.syncFilter":
      case "SyncStream.syncDropMultiple":
      case "SyncStream.syncTimes":
      case "SyncStream.syncTake":
      case "SyncStream.map":
      case "ToptStream.toptFilter":
      case "ToptStream.toptDropMultiple":
      case "ToptStream.toptTake":
      case "ToptStream.toptTimes":
      case "EventStream.eTimes":
      case "EventStream.eDropWhile":
      case "EventStream.eTakeWhile":
      case "EventStream.eDropMultiple":
      case "EventStream.eTake":
      case "EventStream.eFinerTime":
      case "EventStream.eRougherTime":
      case "ControlFunctions.select":
      case "EventStream.eFilter":
      case "EventStream.eNth":
      case "EventStream.eMap": return true;
      default: return false;
    }
  }

  @Override
  public void visit(ASTFieldAccessExpression node) {
    String fqn = ProvisorischerCode.getQualifiedNameOfFunction(node);
    Optional<String> directTargetMapping = mapToIsabelle(fqn);
    if(mapToIsabelleInfix(fqn).isPresent()) {
      return;
    }
    if(directTargetMapping.isPresent()) {
      printer.print(directTargetMapping.get());
      return;
    }
    if(node.getExpression() instanceof ASTFieldAccessExpression) {
      ASTFieldAccessExpression objExpr = (ASTFieldAccessExpression) node.getExpression();
      var previousTypecheck = FocusTool.getPreviousTypecheck();
      var innerType = TypeCheck3Access.typeOf(previousTypecheck, objExpr);
      if(innerType != null && !innerType.isObscureType()) {
        printer.print(
            "(" + innerType.printFullName() + "_get_" + node.getName() + " ");
        return;
      }
    }
    if(node.getExpression() instanceof ASTNameExpression
        && node.getEnclosingScope() instanceof SysMLv2Scope) {
      ASTNameExpression namedExpr = (ASTNameExpression) node.getExpression();
      Optional<VariableSymbol> resolveVar = ((SysMLv2Scope) node.getEnclosingScope()).resolveVariable(namedExpr.getName());
      if(resolveVar.isPresent()) {
        String varType = resolveVar.get().getType().printFullName();
        printer.print("(" + varType + "_get_" + node.getName() + " ");
      }
    }
  }

  @Override
  public void endVisit(ASTFieldAccessExpression node) {
    String fqn = ProvisorischerCode.getQualifiedNameOfFunction(node);
    if(mapToIsabelle(fqn).isPresent() || mapToIsabelleInfix(fqn).isPresent()) {
      return;
    }
    if(node.getExpression() instanceof ASTFieldAccessExpression) {
      printer.print(")");
      return;
    }
    if(node.getExpression() instanceof ASTNameExpression
        && node.getEnclosingScope() instanceof SysMLv2Scope) {
      ASTNameExpression namedExpr = (ASTNameExpression) node.getExpression();
      Optional<VariableSymbol> resolveVar = ((SysMLv2Scope) node.getEnclosingScope()).resolveVariable(
          namedExpr.getName());
      if(resolveVar.isPresent()) {
        printer.print(")");
        return;
      }
    }
    String expressionName = ((ASTNameExpression) node.getExpression()).getName();
    SysMLv2Scope scope = (SysMLv2Scope) node.getEnclosingScope();
    boolean isType = scope.resolveVariable(expressionName).isEmpty()
        && (scope.resolveType(expressionName).isPresent()
        || scope.resolveTypeVar(expressionName).isPresent());
    if(isType) {
      printer.print(".");
      printer.print(node.getName());
    }
  }

  protected Optional<PortUsageSymbol> getPortUsage(ASTFieldAccessExpression node) {
    if(node.getExpression() instanceof ASTNameExpression) {
      String potentialPortUsage = ((ASTNameExpression) node.getExpression()).getName();
      return ((ISysMLPartsScope) node.getEnclosingScope())
          .resolvePortUsage(potentialPortUsage);
    }
    else if(node.getExpression() instanceof ASTFieldAccessExpression
        && ((ASTFieldAccessExpression) node.getExpression()).getExpression() instanceof ASTNameExpression) {
      var namedExpr = (ASTNameExpression) ((ASTFieldAccessExpression) node.getExpression()).getExpression();
      Optional<VariableSymbol> potVar = ((SysMLv2Scope) node.getEnclosingScope())
          .resolveVariable(namedExpr.getName());
      if(potVar.isPresent()) {
        String valType = potVar.get().getType().printFullName();
        String potentialPortUsage = valType + "."
            + ((ASTFieldAccessExpression) node.getExpression()).getName();
        return ((ISysMLPartsScope) node.getEnclosingScope())
            .resolvePortUsage(potentialPortUsage);
      }
      return Optional.empty();
    }
    else if(node.getExpression() instanceof ASTArrayAccessExpression
        && ((ASTArrayAccessExpression) node.getExpression()).getExpression() instanceof ASTNameExpression) {
      String potentialPortUsage = ((ASTNameExpression) ((ASTArrayAccessExpression) node.getExpression()).getExpression()).getName();
      return ((ISysMLPartsScope) node.getEnclosingScope())
          .resolvePortUsage(potentialPortUsage);
    }
    else {
      return Optional.empty();
    }
  }

  @Override
  public void handle(ASTFieldAccessExpression node) {
    Optional<PortUsageSymbol> portUsage = getPortUsage(node);
    if(node.getExpression() instanceof ASTArrayAccessExpression
        && portUsage.isPresent()) {
      printer.print("(nth ");
      printer.print(
          portUsage.get().getName() + Constants.SEP + node.getName() + " ");
      ((ASTArrayAccessExpression) node.getExpression()).getIndexExpression().accept(
          getTraverser());
      printer.print(")");
    }
    else if(portUsage.isPresent()) {
      printer.print("channel_" + portUsage.get().getName().replace('.', '_')
          + "_" + node.getName().replace('.', '_') + "_pattern"
      );
    }
    else {
      super.handle(node);
    }
  }

  @Override
  public void visit(ASTArrayAccessExpression node) {
    printer.print("nth ");
  }

  @Override
  public void handle(ASTArrayAccessExpression node) {
    traverser.visit((ASTExpression) node);
    traverser.visit((ASTCommonExpressionsNode) node);
    traverser.visit(node);
  }

  @Override
  public void traverse(ASTArrayAccessExpression node) {
    traverser.visit((ASTExpression) node);
    traverser.visit((ASTCommonExpressionsNode) node);
    traverser.visit(node);
  }
}

