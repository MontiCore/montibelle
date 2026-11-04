part def TestWithoutAccept {
  port input: Booleans;

  exhibit state behavior {
    entry; then S;

    state S;

    transition ok
      first S
      accept input.val
      then S;

    transition bad
      first S
      then S;
  }
}
