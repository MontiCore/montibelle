part def Scheduler_HLR3
  specializes Scheduler_HLR2
{
  port input: ~Packets;
  port output: Packets;

  attribute capacity: nat;

  part buffer: Buffer_HLR3;
  part capacity: Capacity_HLR3 { attribute cap = capacity; }

  connect input to buffer.input;
  connect buffer.output to capacity.input;
  connect capacity.control to buffer.control;
  connect capacity.output to output;
}