package extension.comparator;

import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Assertions.fail;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class FileComparator {

  private static final String FAIL_NOT_EQUAL_MESSAGE =
      "The generated <%s> differed from the expected outcome. The expected outcome was "
          + "overwritten. To see the differences, you might want to inspect the file with a Diff "
          + "tool (e.g. your GIT client). Note: This test will not fail again, unless you undo the "
          + "changes (e.g. through your GIT client). If this failure was expected and you manually "
          + "checked the changes, then you can ignore this error message and run the test again.";

  private Map<Path, String> fileContentMap = new LinkedHashMap<>();

  public void setUp(List<Path> files) {
    for (Path file : files) {
      try {
        String content = new String(Files.readAllBytes(file));
        fileContentMap.put(file, content);
      }
      catch (IOException e) {
        fail("Could not read the expected outcome before starting the test.", e);
      }
    }
  }

  public void check() {
    for (Path file : fileContentMap.keySet()) {
      try {
        String actual = new String(Files.readAllBytes(file));
        String expected = fileContentMap.get(file);
        assertThat(actual).withFailMessage(FAIL_NOT_EQUAL_MESSAGE, file.toString())
            .isEqualTo(expected);
      }
      catch (IOException e) {
        fail("Could not read the outcome after running the test.", e);
      }
    }
  }
}
