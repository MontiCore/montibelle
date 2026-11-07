part def Flasher_HLR2 refines Flasher_HLR {
    port input: ~Booleans;
    port output: Booleans;

    part and1: And_HLR;
    part not1: StrongNot_HLR;

    connect input to and1.input1;
    connect not1.output to and1.input2;
    connect and1.output to not1.input;
    connect and1.output to output;
}