part def A_LLR 
  specializes A_HLR
{
  port groundIn: ~Packets;
  port b1In: ~Packets;
  port b2In: ~Packets;
  port groundOut: Packets;
  port b1Out: Packets;
  port b2Out: Packets;

  part coca: Camera;
  part maniac: M;
  part dfp: DFP;
  part mirmis: Mi;
  part tele: TelecommandAndTelemetry_LLR;

  connect groundIn to tele.groundIn;
  connect tele.cocaOut to coca.input;
  connect tele.maniacOut to maniac.input;
  connect tele.dfpOut to dfp.input;
  connect tele.mirmisOut to mirmis.input;

  connect b1In to tele.b1In;
  connect b2In to tele.b2In;
  connect coca.output to tele.cocaIn;
  connect maniac.output to tele.maniacIn;
  connect dfp.output to tele.dfpIn;
  connect mirmis.output to tele.mirmisIn;

  connect tele.groundOut to groundOut;
  connect tele.b1Out to b1Out;
  connect tele.b2Out to b2Out;
}