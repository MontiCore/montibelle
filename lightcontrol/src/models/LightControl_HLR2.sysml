private import ModelingMetadata::refinement;

part def LightControl_HLR2 {
  port switchstatus: Booleans;
  port alarmstatus: Booleans;
  port onOffCmd: ~Booleans;

  part 'not': Not_HLR;
  part flasher: Flasher_HLR;
  part 'and': And_HLR;
  part 'or': Or_HLR;

  connect switchstatus to 'and'.input1;
  connect alarmstatus to 'not'.input;
  connect 'not'.output to 'and'.input2;
  connect 'and'.output to 'or'.input1;
  connect alarmstatus to flasher.input;
  connect flasher.output to 'or'.input2;
  connect 'or'.output to onOffCmd;

  #refinement dependency LightControl_HLR2 to LightControl_HLR1;
}