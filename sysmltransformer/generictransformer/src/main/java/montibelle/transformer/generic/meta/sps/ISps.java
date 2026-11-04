package montibelle.transformer.generic.meta.sps;

import montibelle.focus._ast.ASTParameter;
import montibelle.focus._symboltable.TimingSymbol;
import montibelle.transformer.generic.meta.IIdentifiable;
import montibelle.transformer.generic.meta.bundle.IBundle;

import java.util.Collections;
import java.util.List;

public interface ISps extends IIdentifiable {

  default List<ASTParameter> getParameters() {
    return Collections.emptyList();
  }

  IBundle getInput();

  IBundle getOutput();

  boolean isStrongCausal();

  default TimingSymbol getTiming() {
    return getInput().getTimingSymbol();
  }

}
