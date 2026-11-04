#tsyn part def Eve_HLR {
  port input: ~Data_Bool_Tuples;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    assert constraint output {
      (all UntimedStream<Boolean>)->exists {
        in ora: UntimedStream;
        output.val == input.val.syncBoolFilter(ora)
          & ora.setFilter({true}).len() == INF
      }
    }
  }
}
