package montibelle.focus._symboltable;

import de.se_rwth.commons.logging.Log;
import montibelle.focus.FocusMill;
import montibelle.focus._ast.ASTComposition;
import montibelle.focus._ast.ASTEventAutomaton;
import montibelle.focus._ast.ASTInstance;
import montibelle.focus._ast.ASTSpecification;
import montibelle.focus._ast.ASTStateSpace;

import java.util.Optional;

public class FocusScopesGenitor extends FocusScopesGenitorTOP {

  @Override
  public void visit(ASTSpecification node) {
    var symbol = FocusMill.specificationSymbolBuilder()
        .setName(node.getFqn())
        .build();

    if (getCurrentScope().isPresent()) {
      getCurrentScope().get().add(symbol);
    } else {
      Log.warn("0xA5021x81983 Symbol cannot be added to current scope, since no scope exists.");
    }
    symbol.setAstNode(node);

    node.setSymbol(symbol);
    node.setEnclosingScope(symbol.getEnclosingScope());

    initSpecificationHP1(node.getSymbol());
  }

  @Override
  public void visit(ASTInstance node) {
    var symbol = FocusMill.instanceSymbolBuilder()
        .setName(node.getFqn())
        .build();

    if (getCurrentScope().isPresent()) {
      getCurrentScope().get().add(symbol);
    } else {
      Log.warn("0xA5021x59476 Symbol cannot be added to current scope, since no scope exists.");
    }
    symbol.setAstNode(node);

    node.setSymbol(symbol);
    node.setEnclosingScope(symbol.getEnclosingScope());

    initInstanceHP1(node.getSymbol());
  }

  @Override
  public void visit(ASTComposition node) {
    var symbol = FocusMill.compositionSymbolBuilder()
        .setName(node.getFqn())
        .build();

    if (getCurrentScope().isPresent()) {
      getCurrentScope().get().add(symbol);
    } else {
      Log.warn("0xA5021x81983 Symbol cannot be added to current scope, since no scope exists.");
    }
    symbol.setAstNode(node);

    node.setSymbol(symbol);
    node.setEnclosingScope(symbol.getEnclosingScope());

    initCompositionHP1(node.getSymbol());
  }

  @Override
  public void visit(ASTEventAutomaton node) {
    var symbol = FocusMill.eventAutomatonSymbolBuilder()
        .setName(node.getFqn())
        .build();

    if (getCurrentScope().isPresent()) {
      getCurrentScope().get().add(symbol);
    } else {
      Log.warn("0xA5021x81983 Symbol cannot be added to current scope, since no scope exists.");
    }
    symbol.setAstNode(node);

    node.setSymbol(symbol);
    node.setEnclosingScope(symbol.getEnclosingScope());

    initEventAutomatonHP1(node.getSymbol());
  }

  @Override
  public void visit(ASTStateSpace node) {
    if (!node.isPresentSymbol()) {
      super.visit(node);
    }
  }
}
