part def BoolInverter{
  port input: Bool;
  port output: ~Bool;

  assert constraint InverterConstraint {
    input.val == <true> implies output.val == <false>
  }
}
