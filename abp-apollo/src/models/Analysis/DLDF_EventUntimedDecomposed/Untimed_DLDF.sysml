private import VerificationLibrary::untimed;

#untimed part def 'Event-driven Untimed DLDF' 
    specializes Untimed_DLDF_HLR3, Untimed_DLDF_HLR2, Untimed_DLDF_HLR1
{
  :>> scheduler1: Untimed_Scheduler_LLR { :>> scheduler1.capacity = cap1; }
  :>> scheduler2: Untimed_Scheduler_LLR { :>> scheduler1.capacity = cap2; }
  :>> scheduler3: Untimed_Scheduler_LLR { :>> scheduler1.capacity = cap3; }
  :>> scheduler4: Untimed_Scheduler_LLR { :>> scheduler1.capacity = cap4; }

  connect input1 to scheduler1.input;
  connect input2 to scheduler2.input;
  connect input3 to scheduler3.input;
  connect input4 to scheduler4.input;

  connect scheduler1.output to output1;
  connect scheduler2.output to output2;
  connect scheduler3.output to output3;
  connect scheduler4.output to output4;
}