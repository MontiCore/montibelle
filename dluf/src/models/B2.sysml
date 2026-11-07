part def B2 {
  port input: ~Packets;
  port output: Packets;

  satisfy requirement r1 {
    assume constraint c {
      input.data.len() == INF
    }
  }
}