part def And_LLR specializes And_HLR {
  port input1: ~Booleans;
  port input2: ~Booleans;
  port output: Booleans;

  exhibit state behavior {
    entry;
      then S;

    state S;

    transition
      first S
      if input1.val == true & input2.val == true
      do action { send true to output.val; }
      then S;
    
    transition 
      first S
      if !(input1.val == true & input2.val == true)
      do action { send false to output.val; }
      then S;
  }
}
