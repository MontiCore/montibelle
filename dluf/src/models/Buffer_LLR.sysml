part def Buffer_LLR
  specializes Buffer_HLR3
{
  timing instant;
  
  port input: ~Packets;
  port control: ~Ctrl;
  port output: Packets;

  exhibit state BufferAutomaton {
    entry action {
      assign old_packets := new List<Packet>();
      assign new_packets := new List<Packet>();
    }

    then S;

    state S;
    attribute old_packets: List<Packet>;
    attribute new_packets: List<Packet>;

    transition
      first S
      accept input.data
      if old_packets.count() == 0
      do action {
        assign new_packets := new_packets.append(new List<Packet>(input.data));
        send input.data to output.data;
      }
      then S;

    transition
      first S
      accept input.data
      if old_packets.count() > 0
      do action { assign new_packets := new_packets.append(new List<Packet>(input.data)); }
      then S;

    transition
      first S
      accept control.data
      if control.data == CtrlEnum.ACK && old_packets.count() > 1
      do action { assign old_packets := old_packets.tail(); }
      then S;

    transition
      first S
      accept control.data
      if control.data == CtrlEnum.ACK && old_packets.count() == 1
      do action {
        assign old_packets := old_packets.tail();
        send new_packets to output.data;
      }
      then S;

    transition
      first S
      accept control.data
      if control.data == CtrlEnum.NAK && old_packets.count() > 0
      do action {
        send old_packets.append(new_packets) to output.data;
        assign new_packets := old_packets.append(new_packets);
        assign old_packets := new List();
      }
      then S;

    transition
      first S
      accept control.data
      if old_packets.count() == 0
      then S;
  
    transition
      first S
      accept Tick
      do action {
        assign old_packets := new_packets;
        assign new_packets := new List();
      }
      then S;
  }
}
