#tsyn part def Decrypt2_HLR {
  port input: ~Booleans;
  port output: Booleans;

  satisfy requirement MsgProcessing {
    require constraint output {
      output.val == input.val.map(Not)
    }
  }
}
