part def DoubleInverter_Spec {
  port input: Booleans;
  port output: ~Booleans;

  assert constraint double_inverter_behavior {
    forall long k:
      input.val == <true>.times(k) implies output.val == <true>.times(k)
  }
}
