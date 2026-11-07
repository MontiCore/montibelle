private import VerificationLibrary::*;
private import Streams::'∞';
private import Streams::Tick;
private import ScalarValues::*;
private import ControlFunctions::**;
private import SequenceFunctions::**;
private import Functions::**;

part def 'Atomic DLDF' {
  port cmd:   ~Packets;
  port voice: ~Packets;
  port tele:  ~Packets;
  port vid:   ~Packets;

  port o: Packets;

  attribute mcap1: Natural;
  attribute mcap2: Natural;
  attribute mcap3: Natural;
  attribute mcap4: Natural;

  exhibit state {
    attribute cap1: Natural;
    attribute cap2: Natural;
    attribute cap3: Natural;
    attribute cap4: Natural;
    attribute queue1: Packet[*] ordered;
    attribute queue2: Packet[*] ordered;
    attribute queue3: Packet[*] ordered;
    attribute queue4: Packet[*] ordered;

    entry action {
      assign cap1 := mcap1;
      assign cap2 := mcap2;
      assign cap3 := mcap3;
      assign cap4 := mcap4;
    }
    then state S;

    transition
      first S
      accept p: Packet via cmd
      if p.size <= cap1 & queue1->isEmpty()
      do action { send p to o; assign cap1 := cap1-p.size; }
      then S;

    transition
      first S
      accept p: Packet via voice
      if p.size <= cap2 & queue2->isEmpty()
      do action { send p to o; assign cap2 := cap2-p.size; }
      then S;
    
    transition
      first S
      accept p: Packet via tele
      if p.size <= cap3 & queue3->isEmpty()
      do action { send p to o; assign cap3 := cap3-p.size; }
      then S;

    transition
      first S
      accept p: Packet via vid
      if p.size <= cap4 & queue4->isEmpty()
      do action { send p to o; assign cap4 := cap4-p.size; }
      then S;

    transition
      first S
      accept p: Packet via cmd
      if p.size > cap1
      do assign queue1 := queue1->add(p)
      then S;

    transition
      first S
      accept p: Packet via voice
      if p.size > cap2
      do assign queue2 := queue2->add(p)
      then S;

    transition
      first S
      accept p: Packet via tele
      if p.size > cap3
      do assign queue3 := queue3->add(p)
      then S;

    transition
      first S
      accept p: Packet via vid
      if p.size > cap4
      do assign queue4 := queue4->add(p)
      then S;

    transition
      first S
      accept Tick
      do action {
        send takemcap(mcap1, queue1)
          ->add(takemcap(mcap2, queue2)) 
          ->add(takemcap(mcap3, queue3)) 
          ->add(takemcap(mcap4, queue4)) 
        to o;
        assign cap1 := mcap1 - lsize(takemcap(mcap1, queue1));
        assign cap2 := mcap2 - lsize(takemcap(mcap2, queue2));
        assign cap3 := mcap3 - lsize(takemcap(mcap3, queue3));
        assign cap4 := mcap4 - lsize(takemcap(mcap4, queue4));
      }
      then S;

  }
}