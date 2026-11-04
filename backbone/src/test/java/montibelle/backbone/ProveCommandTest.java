package montibelle.backbone;

import org.junit.jupiter.api.Test;

import java.nio.file.Paths;

import static java.util.List.of;
import static org.assertj.core.api.Assertions.assertThat;

public class ProveCommandTest {

  @Test
  public void testDefaultCommand() {
    var p = new ProveCommand();
    assertThat(p.getCommand()).isEqualTo("autosledgi prove");
  }

  @Test
  public void testCommand() {
    var p = new ProveCommand(Paths.get("a"), of(Paths.get("b")), "c", Paths.get("p"), 5, true, Paths.get("d"));
    assertThat(p.getCommand())
        .isEqualTo("autosledgi prove --cloud -d b --prover-timeout 5 --project p --session c --log d a");
  }

}
