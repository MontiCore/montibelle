part def StrongNot_LLR specializes StrongNot_HLR {
  port input: ~Booleans;
  port output: Booleans;

  exhibit state behavior {
    entry;
      do action { send true to output.val; }
      then S;

    state S;

    transition
      first S
      if input.val == Eps 
      do action { send Eps to output.val; }
      then S;

    transition
      first S
      if input.val != Eps
      do action { send !input.val to output.val; }
      then S;
  }
}
