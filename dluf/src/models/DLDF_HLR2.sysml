part def DLDF_HLR2
  specializes DLDF_HLR1
{
  port input1: ~Packets;
  port input2: ~Packets;
  port input3: ~Packets;
  port input4: ~Packets;

  port output1: Packets;
  port output2: Packets;
  port output3: Packets;
  port output4: Packets;

  attribute cap1: nat;
  attribute cap2: nat;
  attribute cap3: nat;
  attribute cap4: nat;

  part scheduler1: Scheduler_HLR2 { attribute capacity = cap1; }
  part scheduler2: Scheduler_HLR2 { attribute capacity = cap2; }
  part scheduler3: Scheduler_HLR2 { attribute capacity = cap3; }
  part scheduler4: Scheduler_HLR2 { attribute capacity = cap4; }

  connect input1 to scheduler1.input;
  connect input2 to scheduler2.input;
  connect input3 to scheduler3.input;
  connect input4 to scheduler4.input;

  connect scheduler1.output to output1;
  connect scheduler2.output to output2;
  connect scheduler3.output to output3;
  connect scheduler4.output to output4;
}