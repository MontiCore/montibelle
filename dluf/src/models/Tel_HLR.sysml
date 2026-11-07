part def Tel_HLR {
  port groundIn: ~Packets;
  port b1In: ~Packets;
  port b2In: ~Packets;
  port cocaIn: ~Packets;
  port mIn: ~Packets;
  port dfpIn: ~Packets;
  port miIn: ~Packets;
  port groundOut: Packets;
  port b1Out: Packets;
  port b2Out: Packets;
  port cocaOut: Packets;
  port mOut: Packets;
  port dfpOut: Packets;
  port miOut: Packets;

  part router: Router;
  part sorter: Sorter;
  part mergex: Merge_LLR;
  part dldf: DLDF_HLR1{
    attribute cap1 = 400;
    attribute cap2 = 300;
    attribute cap3 = 200;
    attribute cap4 = 100;
  }

  connect groundIn to router.input;
  connect router.cocaOut to cocaOut;
  connect router.mOut to mOut;
  connect router.dfpOut to dfpOut;
  connect router.miOut to miOut;
  connect router.b1Out to b1Out;
  connect router.b2Out to b2Out;

  connect b1In to sorter.b1In;
  connect b2In to sorter.b2In;
  connect cocaIn to sorter.cocaIn;
  connect mIn to sorter.mIn;
  connect dfpIn to sorter.dfpIn;
  connect miIn to sorter.miIn;

  connect sorter.prio1 to dldf.input1;
  connect sorter.prio2 to dldf.input2;
  connect sorter.prio3 to dldf.input3;
  connect sorter.prio4 to dldf.input4;

  connect dldf.output1 to mergex.input1;
  connect dldf.output2 to mergex.input2;
  connect dldf.output3 to mergex.input3;
  connect dldf.output4 to mergex.input4;

  connect mergex.output to groundOut;

}