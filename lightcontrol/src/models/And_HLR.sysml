private import ScalarValues::Boolean;

part def And_HLR {
  port input1: Booleans;
  port input2: Booleans;
  port output: ~Booleans;

  assert constraint {
    output.val == input1.val.zip(input2.val)
      .map{ in p:(Boolean,Boolean); p.fst & p.snd }
  }

}