#tsyn part def Alice_HLR {
  port input: ~Data;
  port control: ~Booleans;
  port output: Data_Bool_Tuples;

  satisfy requirement MsgProcessing {
    assume constraint {
      input.val.len() == INF & control.val.len() == INF
    }
    assert constraint test {
      UntimedStream.uProjFst(output.val.untimed().rcDups()) \sqsubseteq input.val.untimed()
      &
      UntimedStream.uProjSnd(output.val.untimed().rcDups()).rcDups()
        == UntimedStream.uProjSnd(output.val.untimed().rcDups())
      &
      control.val.rcDups().len() < input.val.len()
        implies output.val.len() == INF
      &
      SyncStream.syncProjFst(output.val.rcDups()).len()
        == min(input.val.len(), 1 + control.val.rcDups().len())
    }
  }
}
