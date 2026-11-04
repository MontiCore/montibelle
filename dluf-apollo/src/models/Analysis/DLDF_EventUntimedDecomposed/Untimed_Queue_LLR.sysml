private import VerificationLibrary::untimed;
private import ScalarValues::**;
private import SequenceFunctions::**;

#untimed part def Untimed_Queue_LLR specializes Untimed_Queue_HLR3 {

  exhibit state {
    attribute old_packets: Packet[*] ordered;
    attribute new_packets: Packet[*] ordered;

    entry action {
      assign old_packets := ();
      assign new_packets := ();
    }
    then S;

    state S;

    transition
      first S
      accept Packet via input
      if old_packets->size() == 0
      do action {
        assign new_packets := new_packets->add(input.data);
        send input.data to output;
      }
      then S;

    transition
      first S
      accept p: Packet via input
      if old_packets->size() > 0
      do action { assign new_packets := new_packets->add(p); }
      then S;

    transition
      first S
      accept p: Packet via control
      if p == CtrlEnum::ACK & old_packets->size() > 1
      do action { assign old_packets := old_packets->tail(); }
      then S;

    transition
      first S
      accept p: Packet via control
      if p == CtrlEnum::ACK & old_packets->size() == 1
      do action {
        assign old_packets := old_packets->tail();
        send new_packets to output;
      }
      then S;

    transition
      first S
      accept p: Packet via control
      if control.data == CtrlEnum::NAK & old_packets->size() > 0
      do action {
        send old_packets->add(new_packets) to output;
        assign new_packets := old_packets->add(new_packets);
        assign old_packets := ();
      }
      then S;

    transition
      first S
      accept p: Packet via control
      if old_packets->size() == 0
      then S;
  
    transition
      first S
      accept p: Packet via control
      do action {
        assign old_packets := new_packets;
        assign new_packets := ();
      }
      then S;
  }
}
