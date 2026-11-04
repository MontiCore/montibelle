part def Merge_LLR {
  port input1: ~Packets;
  port input2: ~Packets;
  port input3: ~Packets;
  port input4: ~Packets;
  port output: Packets;

  exhibit state MergeAutomaton {
    entry; then S;
    state S;

    transition
      first S
      accept input1.data
      do action { send input1.data to output.data; }
      then S;

    transition
      first S
      accept input2.data
      do action { send input2.data to output.data; }
      then S;

    transition
      first S
      accept input3.data
      do action { send input3.data to output.data; }
      then S;

    transition
      first S
      accept input4.data
      do action { send input4.data to output.data; }
      then S;
  }
}