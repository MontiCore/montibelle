#tsyn part def Decrypt1_HLR {
  port input: ~Nat_Bool_Tuples;
  port output: Nat_Bool_Tuples;

  satisfy requirement MsgProcessing {

    assert constraint output {
      output.val == SyncStream.syncProjFst(input.val).map(Decrypt).zip(SyncStream.syncProjSnd(input.val).map(Not))
    }
  }
}
