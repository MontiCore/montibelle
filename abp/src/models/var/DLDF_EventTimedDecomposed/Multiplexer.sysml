part def Multiplexer {
  port input1: ~Packets;
  port input2: ~Packets;
  port input3: ~Packets;
  port input4: ~Packets;
  port output: Packets;

  exhibit state {
    entry; then S;
    state S;

    transition
      first S
      accept Packet via input1
      do action { send input1.data to output; }
      then S;

    transition
      first S
      accept Packet via input2
      do action { send input2.data to output; }
      then S;

    transition
      first S
      accept Packet via input3
      do action { send input3.data to output; }
      then S;

    transition
      first S
      accept Packet via input4
      do action { send input4.data to output; }
      then S;
  }
}