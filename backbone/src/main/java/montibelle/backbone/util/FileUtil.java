package montibelle.backbone.util;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Comparator;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

public class FileUtil {

  private FileUtil() {
  }

  public static boolean fileContainsPattern(Path filePath, String pattern) throws IOException {
    String content = new String(Files.readAllBytes(filePath));
    Pattern p = Pattern.compile(pattern);
    Matcher m = p.matcher(content);
    return m.find();
  }

  public static void deleteDirectory(Path directoryToBeDeleted) throws IOException {
    if (Files.exists(directoryToBeDeleted)) {
      List<Path> delete = Files.walk(directoryToBeDeleted).sorted(Comparator.reverseOrder())
          .collect(Collectors.toList());
      for (Path path : delete) {
        Files.deleteIfExists(path);
      }
    }
  }

  public static void copyDirectory(String sourceDirectoryLocation, String destinationDirectoryLocation)
      throws IOException {
    Files.walk(Paths.get(sourceDirectoryLocation))
        .forEach(source -> {
          Path destination = Paths.get(destinationDirectoryLocation, source.toString()
              .substring(sourceDirectoryLocation.length()));
          try {
            Files.copy(source, destination);
          }
          catch (IOException e) {
            e.printStackTrace();
          }
        });
  }
}
