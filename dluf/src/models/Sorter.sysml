part def Sorter {
  port b1In: ~Packets;
  port b2In: ~Packets;
  port cocaIn: ~Packets;
  port mIn: ~Packets;
  port dfpIn: ~Packets;
  port miIn: ~Packets;
  port prio1: Packets;
  port prio2: Packets;
  port prio3: Packets;
  port prio4: Packets;
  
  satisfy requirement r {
    assume constraint c {
      b1In.data.len() == INF
    }
  }
}
