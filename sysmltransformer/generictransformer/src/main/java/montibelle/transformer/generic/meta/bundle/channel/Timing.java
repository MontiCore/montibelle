package montibelle.transformer.generic.meta.bundle.channel;

public enum Timing implements ITiming {

  SYNC,
  TONE,
  EVENT;

  @Override
  public boolean isEventBased() {
    return this == EVENT;
  }

  @Override
  public boolean isTimeSyncronous() {
    return this == SYNC;
  }

  @Override
  public boolean isStrictlyTimeSyncronous() {
    return this == TONE;
  }

  @Override
  public String getName() {
    return name();
  }
}
