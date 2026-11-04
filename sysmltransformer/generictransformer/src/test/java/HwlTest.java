import montibelle.transformer.generic.hwls.*;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;

import static org.assertj.core.api.Assertions.assertThat;

public class HwlTest {

  private final static String BASE = "src/test/resources/montibelle/transformer/generic/hwls";

  private static Path ACTUAL = Path.of(BASE).resolve("Hwls.yaml");
  private static Path EXPECTED = Path.of(BASE).resolve("Expected.yaml");

  private void check(AHwlProvider provider) {
    assertThat(provider.getHwls("session", "Filename")).hasSize(1);
    assertThat(provider.getHwls("session", "Filename").get(0).getFilename()).isEqualTo("HwlFile");
    assertThat(provider.getHwls("session", "Filename").get(0).getSessionName()).isEqualTo("hwlSession");
    assertThat(provider.getHwls("session", "Filename").get(0).getType()).isEqualTo(HwlType.PROLOGUE);
  }

  @Test
  @Disabled("addHwl is not yet implemented for FilebasedHwlProvider")
  public void testFilebasedWrite() throws IOException {
    var provider = new FilebasedHwlProvider(ACTUAL);
    provider.addHwl("session", "Filename", new HwlTheory("HwlFile", "hwlSession", HwlType.PROLOGUE));

    check(provider);

    assertThat(Files.readString(ACTUAL)).isEqualTo(Files.readString(EXPECTED));
  }

  @Test
  public void testFilebasedRead() {
    var provider = new FilebasedHwlProvider(EXPECTED);
    check(provider);
  }

  @Test
  public void testGettingNonSpecified() {
    var provider = new FilebasedHwlProvider(EXPECTED);

    assertThat(provider.getHwls("doesNotExist", "Filename")).hasSize(0);
    assertThat(provider.getHwls("session", "DoesNotExist")).hasSize(0);
    assertThat(provider.getHwls("doesNotExist", "DoesNotExist")).hasSize(0);

    assertThat(provider.getPrologueImportsFor("doesNotExist", "Filename")).hasSize(0);
    assertThat(provider.getPrologueImportsFor("session", "DoesNotExist")).hasSize(0);
    assertThat(provider.getPrologueImportsFor("doesNotExist", "DoesNotExist")).hasSize(0);
    assertThat(provider.getEpilogueImportsFor("doesNotExist", "Filename")).hasSize(0);
    assertThat(provider.getEpilogueImportsFor("session", "DoesNotExist")).hasSize(0);
    assertThat(provider.getEpilogueImportsFor("doesNotExist", "DoesNotExist")).hasSize(0);

  }

  @Test
  public void testInMemory() {
    var provider = new InMemoryHwlProvider();
    assertThat(provider.getHwls("session", "Filename")).hasSize(0);

    provider.addHwl("session", "Filename", new HwlTheory("HwlFile", "hwlSession", HwlType.PROLOGUE));
    check(provider);
  }

  @AfterEach
  public void clean() throws IOException {
    try {
      Files.delete(ACTUAL);
    }
    catch(NoSuchFileException ex) {
    }
  }

}
