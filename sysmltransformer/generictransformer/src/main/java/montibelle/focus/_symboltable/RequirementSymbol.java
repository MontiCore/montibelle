package montibelle.focus._symboltable;

public class RequirementSymbol extends RequirementSymbolTOP {

  private SpsSymbol subjectSymbol;

  public RequirementSymbol(String name) {
    super(name);
  }

  public SpsSymbol getSubjectSymbol() {
    return subjectSymbol;
  }

  public void setSubjectSymbol(SpsSymbol subjectSymbol) {
    this.subjectSymbol = subjectSymbol;
  }
}
