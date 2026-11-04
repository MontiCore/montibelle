part def Inverter_HLR2 specializes Inverter_HLR1 {
  port input: Booleans;
  port output: ~Booleans;

  satisfy requirement InverterRequirement2 {
    require constraint InverterConstraint2 {
      forall long k: input.val == <true>.times(k) implies output.val == <false>.times(k)
    }
  }
}
