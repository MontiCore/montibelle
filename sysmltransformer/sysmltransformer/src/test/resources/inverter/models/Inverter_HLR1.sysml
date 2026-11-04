part def Inverter_HLR1 {
  port input: Booleans;
  port output: ~Booleans;

  assert constraint InverterConstraint {
    input.val == <true> implies output.val == <false>
  }
}
