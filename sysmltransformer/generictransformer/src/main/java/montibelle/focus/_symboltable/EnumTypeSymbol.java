package montibelle.focus._symboltable;

import jline.internal.Log;
import montibelle.transformer.generic.Constants;

import java.util.List;

public class EnumTypeSymbol extends EnumTypeSymbolTOP {

  public EnumTypeSymbol(String name) {
    super(name);
  }

  public String getSanitizedName() {
    return name.replaceAll("[^A-Za-z0-9]", "");
  }

  @Override
  public boolean isFinite() {
    return Constants.FINITE_TYPES.containsKey(name);
  }

  @Override
  public List<String> getFiniteChoicesList() {
    if(finiteChoices != null && !finiteChoices.isEmpty()) {
      return finiteChoices;
    }
    else if(isFinite()) {
      return Constants.FINITE_TYPES.get(name);
    }
    else {
      Log.error(String.format(
          "Tried to list the choices for non-finite type '%s'.", name));
    }
    return null;
  }

}
