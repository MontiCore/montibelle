package montibelle.focus._ast;

import org.jetbrains.annotations.NotNull;

public class ASTIAutomaton extends ASTIAutomatonTOP {

  @NotNull @Override
  public String getName() {
    return de.se_rwth.commons.Names.getSimpleName(getFqn());
  }

}
