part def System_HLR {
  port user1: ~Packets;
  port user2: ~Packets;
  port user3: ~Packets;
  port user4: ~Packets;
  port link: Packets;

  part dluf: DLUF_HLR1 {
    attribute cap1 = 400;
    attribute cap2 = 300;
    attribute cap3 = 200;
    attribute cap4 = 100;
  }
  part mergex: Merge_LLR;

  connect user1 to dluf.input1;
  connect user2 to dluf.input2;
  connect user3 to dluf.input3;
  connect user4 to dluf.input4;

  connect dluf.output1 to mergex.input1;
  connect dluf.output2 to mergex.input2;
  connect dluf.output3 to mergex.input3;
  connect dluf.output4 to mergex.input4;

  connect mergex.output to link;
}
