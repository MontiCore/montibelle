package test;

<<deterministic>>
component SimpleComp {
  timing causalsync;

  boolean boolPort;

  automaton {
    state A;
    initial A;
  }
}
