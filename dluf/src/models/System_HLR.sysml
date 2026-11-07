part def System_HLR {
  port groundIn: ~Packets;
  port groundOut: Packets;

  part a: A_HLR;
  part b1: B1;
  part b2: B2;

  connect groundIn to a.groundIn;
  connect a.b1Out to b1.input;
  connect a.b2Out to b2.input;
  connect a.groundOut to groundOut;
  connect b1.output to a.b1In;
  connect b2.output to a.b2In;
}
