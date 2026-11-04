package montibelle.transformer.generic.meta.sps;

import java.util.Collections;
import java.util.List;

public interface ISpecification extends ISps {

  default List<String> getAssumptions() {
    return Collections.emptyList();
  }

  List<String> getPredicates();
}
