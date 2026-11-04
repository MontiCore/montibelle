package spec;

import java.lang.*;

component Refined refines Rough {

  timing sync;

  port
    in int i,
    out boolean o;

  spec {
    forall t in Integer: (
      (i >= 0) implies (
        (i > 10) implies (o.nth(t) == true)
        && o.nth(t) != null
      )
    );
  }
}
