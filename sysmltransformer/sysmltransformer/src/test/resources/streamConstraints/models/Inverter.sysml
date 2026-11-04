private import VerificationLibrary::tsyn;
private import Streams::SyncStream;
private import ScalarValues::Boolean;

#tsyn part def Inverter {
  port i: Booleans;
  port o: ~Booleans;

  satisfy requirement Inverter {
    attribute i_history: SyncStream { :>> E: Boolean; }
    attribute o_history: SyncStream { :>> E: Boolean; }
    connect i to i_history;
    connect o to o_history;

    require constraint Inversion {
      o_history == i_history->SyncStream::map { in b: Boolean; not b }
    }
  }
}
