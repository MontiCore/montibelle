import montibelle.transformer.generic.meta.bundle.channel.ITiming;
import montibelle.transformer.generic.meta.bundle.channel.Timing;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class TimingTest {

  @Test
  public void testSyncTiming() {
    Assertions.assertTrue(Timing.SYNC.isTimeSyncronous());

    Assertions.assertFalse(Timing.SYNC.isStrictlyTimeSyncronous());
    Assertions.assertFalse(Timing.SYNC.isEventBased());
  }

  @Test
  public void testStrictSyncTiming() {
    Assertions.assertTrue(Timing.TONE.isStrictlyTimeSyncronous());

    Assertions.assertFalse(Timing.TONE.isTimeSyncronous());
    Assertions.assertFalse(Timing.TONE.isEventBased());
  }

  @Test
  public void testEventTiming() {
    Assertions.assertTrue(Timing.EVENT.isEventBased());

    Assertions.assertFalse(Timing.EVENT.isTimeSyncronous());
    Assertions.assertFalse(Timing.EVENT.isStrictlyTimeSyncronous());
  }

  @Test
  public void testITimingDefaultsAreFalse() {
    ITiming t = new ITiming() {
      @Override
      public String getName() {
        return "DUMMY";
      }
    };

    assertThat(t.isEventBased()).isFalse();
    assertThat(t.isTimeSyncronous()).isFalse();
    assertThat(t.isStrictlyTimeSyncronous()).isFalse();
  }
}
