package montibelle.focus._ast;

import montibelle.transformer.generic.Constants;

import java.util.List;

public class ASTChannelType extends ASTChannelTypeTOP {

  public boolean isEventBased() {
    return getTimingSymbol().isEventBased();
  }

  public boolean isFinite() {
    return Constants.FINITE_TYPES.containsKey(name);
  }

  public List<String> finiteChoices() {
    return Constants.FINITE_TYPES.get(name);
  }

}
