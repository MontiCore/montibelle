package montibelle.focus._ast;

import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.TheorySymbolBuilder;
import java.util.List;

public class ASTTheory extends ASTTheoryTOP {

  public ASTTheory clone(String filename) {
    ASTTheory astClone = deepClone();
    astClone.setFilename(filename);
    astClone.setEnclosingScope(this.getEnclosingScope());

    var symbolClone = new TheorySymbolBuilder()
        .setName(astClone.getName())
        .setSessionName(getSymbol().getSessionName())
        .setFilename(astClone.getFilename())
        .setEnclosingScope(getSymbol().getEnclosingScope())
        .setAstNode(astClone)
        .build();

    astClone.setSymbol(symbolClone);

    return astClone;
  }

  public List<String> getPrologueSessions() {
    return FocusMill.getHwlProvider()
        .getProloguesSessionsFor(getSession().getName(), getFilename());
  }

  public List<String> getPrologueImportStatements() {
    return FocusMill.getHwlProvider()
        .getPrologueImportsFor(getSession().getName(), getFilename());
  }

  public List<String> getEpilogueSessions() {
    return FocusMill.getHwlProvider()
        .getEpilogueSessionsFor(getSession().getName(), getFilename());
  }

  public boolean isSubstituted() {
    return FocusMill.getHwlProvider()
        .substituteFor(getSession().getName(), getFilename()) != null;
  }

  @Override
  public String toString() {
    return getSessionName() + "." + getFilename();
  }
}
