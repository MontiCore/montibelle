#tsyn part def SecureProtocol_HLR1 {
  port input: ~Data;
  port output: Data;

  satisfy requirement {
    assume constraint {
      input.val.len() == INF
    }
    require constraint output {
      output.val.untimed() == input.val.untimed()
    }
  }
}
