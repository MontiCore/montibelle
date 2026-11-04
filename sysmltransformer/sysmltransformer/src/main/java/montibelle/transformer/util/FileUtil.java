package montibelle.transformer.util;

import java.io.File;

public final class FileUtil {

  private FileUtil() {
  }

  public static boolean deleteDirectory(File directoryToBeDeleted) {
    File[] allContents = directoryToBeDeleted.listFiles();

    if (allContents != null) {
      for (File file : allContents) {
        deleteDirectory(file);
      }
    }

    return directoryToBeDeleted.delete();
  }
}
