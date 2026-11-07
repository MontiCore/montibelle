part def Camera {
  port input: ~Packets;
  port output: Packets;

  satisfy requirement r {
    assume constraint c {
      input.data.len() == INF
    }
  }
}
