part def Scheduler_LLR
  specializes Scheduler_HLR3, Scheduler_HLR2
{
  port input: ~Packets;
  port output: Packets;

  attribute capacity: nat;

  part buffer: Buffer_LLR;
  part capacity: Capacity_LLR { attribute cap = capacity; }

  connect input to buffer.input;
  connect buffer.output to capacity.input;
  connect capacity.control to buffer.control;
  connect capacity.output to output;
}