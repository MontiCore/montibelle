package montibelle.focus._symboltable;

public class IAutomatonSymbol extends IAutomatonSymbolTOP {

  public IAutomatonSymbol(String name) {
    super(name);
  }

  public TheorySymbol getCodeTheorySymbol() {
    return getEnclosingScope().resolveTheory(getCodeTheoryName()).get();
  }
}
