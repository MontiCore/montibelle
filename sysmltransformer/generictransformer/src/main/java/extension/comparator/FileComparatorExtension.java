package extension.comparator;

import extension.util.ExtensionUtil;
import org.junit.jupiter.api.extension.AfterTestExecutionCallback;
import org.junit.jupiter.api.extension.BeforeTestExecutionCallback;
import org.junit.jupiter.api.extension.ExtensionConfigurationException;
import org.junit.jupiter.api.extension.ExtensionContext;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;

public class FileComparatorExtension
    implements BeforeTestExecutionCallback, AfterTestExecutionCallback {

  private static final ExtensionContext.Namespace NAMESPACE = ExtensionContext.Namespace
      .create(FileComparatorExtension.class);

  private static final String KEY = "file.comparator";

  private static List<Path> getFilesInDir(Path dir, String extension, boolean recursive) {
    Objects.requireNonNull(dir);

    try {
      return Files.walk(dir, recursive ? Integer.MAX_VALUE : 1)
          .filter(f -> !f.toString().contains(".isabelle"))
          .filter(Files::isRegularFile)
          .filter(p -> p.toString().endsWith(extension))
          .collect(Collectors.toList());
    }
    catch (IOException e) {
      throw new ExtensionConfigurationException("Could not list files in dir " + dir.toString());
    }
  }

  @Override
  public void beforeTestExecution(ExtensionContext context) {
    Optional<FileCompare> comparatorAnnotationOpt = ExtensionUtil.findAnnotation(context,
        FileCompare.class);
    if (comparatorAnnotationOpt.isEmpty()) {
      throw new ExtensionConfigurationException(
          "Missing annotation @" + FileCompare.class.getSimpleName());
    }
    FileCompare comparatorAnnotation = comparatorAnnotationOpt.get();
    String extension = comparatorAnnotation.extension();
    Path basePath = Paths.get(comparatorAnnotation.base());
    List<Path> files = Arrays.asList(comparatorAnnotation.value())
        .stream()
        .map(s -> basePath.resolve(s))
        .collect(Collectors.toList());
    boolean recursive = comparatorAnnotation.recursive();

    List<Path> fileList = files.size() > 0 ? files : getFilesInDir(basePath, extension, recursive);

    FileComparator comparator = context.getStore(NAMESPACE).getOrComputeIfAbsent(KEY,
        key -> new FileComparator(), FileComparator.class);
    comparator.setUp(fileList);
  }

  @Override
  public void afterTestExecution(ExtensionContext context) {
    FileComparator comparator = context.getStore(NAMESPACE).get(KEY, FileComparator.class);
    comparator.check();
  }
}
