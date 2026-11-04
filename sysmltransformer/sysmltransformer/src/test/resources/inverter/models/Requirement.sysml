requirement 'Requirement' {
  subject llr1: Inverter_LLR1;
  attribute a: boolean;

  assert constraint {
    llr1.input.val == <a, Tick> implies llr1.output.val == <Tick, !a, Tick>
  }
}
