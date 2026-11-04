package spec;

component Rough {

    timing sync;

    port
        in int i,
        out boolean o;

    spec {
        forall t in Integer: (o.nth(t) == true || o.nth(t) == false);
    }
}
