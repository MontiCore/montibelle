part def Router {
  port input: ~Packets;
  port cocaOut: Packets;
  port mOut: Packets;
  port dfpOut: Packets;
  port miOut: Packets;
  port b1Out: Packets;
  port b2Out: Packets;

  satisfy requirement r {
    assume constraint c {
      input.data.len() == INF
    }
  }
}
