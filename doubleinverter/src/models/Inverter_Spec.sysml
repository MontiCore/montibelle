part def Inverter_Spec {
  port input: Booleans;
  port output: ~Booleans;

  assert constraint inverter_behavior {
    forall long k:
      (input.val == <true>.times(k) implies output.val == <false>.times(k))
      &&
      (input.val == <false>.times(k) implies output.val == <true>.times(k))
  }
}
