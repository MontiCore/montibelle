package montibelle.focus._symboltable;

public class FocusArtifactScope extends FocusArtifactScopeTOP {

  public String toString() {
    return getName() + "   #   \"" + (astNode.isPresent() ? getAstNode() + "\"" : "\"");
  }

}
