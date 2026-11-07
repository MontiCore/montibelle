private import ScalarValues::Boolean;

part def Not_HLR {
  port input: Booleans;
  port output: ~Booleans;

  assert constraint {
    output.val == <true>:input.val.map{ in p:Boolean; not(p) }
  }

}