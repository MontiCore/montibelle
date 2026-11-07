part def Not_LLR specializes Not_HLR {
  port input: ~Booleans;
  port output: Booleans;

  exhibit state behavior {
    entry;
      then S;

    state S;

    transition
      first S
      if input.val == Eps 
      do action { send Eps to output.val; }
      then S;

    transition
      first S
      if !(input.val == Eps)
      do action { send !input.val to output.val; }
      then S;
  }
}