part def B1 {
  port input: ~Packets;
  port output: Packets;

  satisfy requirement r {
    assume constraint c {
      input.data.len() == INF
    }
  }
}