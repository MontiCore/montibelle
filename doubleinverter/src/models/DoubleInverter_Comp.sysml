part def DoubleInverter_Comp refines DoubleInverter_Spec {
  port input: Booleans;
  port output: ~Booleans;

  part inverter1: Inverter_Spec;
  part inverter2: Inverter_Spec;

  connect input to inverter1.input;
  connect inverter1.output to inverter2.input;
  connect inverter2.output to output;
}
