package montibelle.transformer.generic.meta;

import java.util.Collections;
import java.util.List;

import static montibelle.transformer.generic.Constants.SEP;

public interface IIdentifiable {

  default List<String> getPackage() {
    return Collections.emptyList();
  }

  String getName();

  default String getIdentifier() {
    if (getPackage().isEmpty()) {
      return getName();
    }
    else {
      return String.join(String.valueOf(SEP), getPackage()) + SEP + getName();
    }
  }

}
