package montibelle.transformer.generic.theories;

import java.util.ArrayList;
import java.util.List;

public final class DatatypeHelpers {

  public static <E> List<E> orderedUnion(List<? extends E> a, List<? extends E> b) {
    List<E> res = new ArrayList<>(a);
    for (E bs : b) {
      if (!(res.contains(bs))) {
        res.add(bs);
      }
    }
    return res;
  }

  public static <E> List<E> orderedIntersection(List<? extends E> a, List<? extends E> b) {
    List<E> res = new ArrayList<>();
    for (E bs : b) {
      if (a.contains(bs) && !(res.contains(bs))) {
        res.add(bs);
      }
    }
    return res;
  }
}
