part def DLDF_HLR3 specializes DLDF_HLR2, DLDF_HLR1 {
  redefines scheduler1: Scheduler_HLR3 { redefines scheduler1.capacity = cap1; }
  redefines scheduler2: Scheduler_HLR3 { redefines scheduler2.capacity = cap2; }
  redefines scheduler3: Scheduler_HLR3 { redefines scheduler3.capacity = cap3; }
  redefines scheduler4: Scheduler_HLR3 { redefines scheduler4.capacity = cap4; }

  connect input1 to scheduler1.input;
  connect input2 to scheduler2.input;
  connect input3 to scheduler3.input;
  connect input4 to scheduler4.input;

  connect scheduler1.output to output1;
  connect scheduler2.output to output2;
  connect scheduler3.output to output3;
  connect scheduler4.output to output4;
}