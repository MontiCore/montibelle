package epc;

import com.google.common.base.Strings;

import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;

public class Preprocessor {

  private int namePos;
  private int typePos;
  private String relType;
  private String objName;
  private String objType;

  private enum Mode {
    Objects, Object, Diagrams, Relations, Start
  }
  private Mode mode;

  private int defaultIndent = 57;
  private List<String> commonKeys = List.of(
      "Type", "Group", "Description/Definition", "Title 1", "Link 1"
  );

  private Stream<String> input;
  private BufferedWriter output;

  public Preprocessor(Stream<String> input, BufferedWriter output) {
    this.input = input;
    this.output = output;
    this.mode = Mode.Start;
  }

  public Preprocessor(Path inputFile, BufferedWriter output) throws IOException {
    this(Files.lines(inputFile), output);
  }

  public Preprocessor(Path inputFile, Path outputFile) throws IOException {
    this(
        Files.lines(inputFile),
        new BufferedWriter(new FileWriter(outputFile.toFile()))
    );
  }

  public void run() throws IOException {
    input
        .forEach(line -> process(line));
    output.flush();
  }

  public void run(int length) throws IOException {
    input
        .limit(length)
        .forEach(line -> process(line));
    output.flush();
  }

  public void process(String line) {
    try {
      switch (mode) {
        case Start: processStart(line); break;
        case Diagrams: processDiagrams(line); break;
        case Objects: processObjects(line); break;
        case Object: processObject(line); break;
        case Relations: processRelations(line); break;
      }
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  private void processRelations(String line) throws IOException {
    if(line.isEmpty() || line.isBlank()) {
      if(!relType.isEmpty() && !relType.isBlank()) {
        output.write(bridge(relType) + " " + wrap(objName) + " " + wrap(objType));
        output.newLine();
      }
      relType = "";
      objType = "";
      objName = "";
      mode = Mode.Objects;
      return;
    }
    if(line.equals("Graphic")) {

      if(!relType.isEmpty() && !relType.isBlank()) {
        output.write(bridge(relType) + " " + wrap(objName) + " " + wrap(objType));
        output.newLine();
      }
      relType = "";
      objType = "";
      objName = "";

      mode = Mode.Start;
      process(line);
    }
    else if(line.startsWith(" ")) {
      objName += line.substring(namePos);
    }
    else {
      if(relType != null && !relType.isEmpty() && !relType.isBlank()) {
        output.write(bridge(relType) + " " + wrap(objName) + " " + wrap(objType));
        output.newLine();
      }

      relType = line.substring(0, namePos).trim();
      objName = line.substring(namePos, typePos).trim();
      objType = line.substring(typePos).trim();
    }
  }

  private void processDiagrams(String line) throws IOException {
    if(line.isEmpty() || line.isBlank()) {
      return;
    }
    else {
      output.write(wrap(line));
      output.newLine();
      mode = Mode.Start;
    }
  }

  public void processStart(String line) throws IOException {
    if(line.isEmpty() || line.isBlank()) {
      return;
    }
    else if(line.startsWith("Model: ")) {
      var modelName = line.split(":\\s")[1];
      output.write("Model: " + wrap(modelName));
      output.newLine();
      mode = Mode.Diagrams;
    }
    else if(commonKeys.stream().anyMatch(k -> line.startsWith(k+ "  "))) {
      var key = commonKeys.stream()
          .filter(k -> line.startsWith(k + "  "))
          .findFirst().get();
      var groupNameWithSpaces = line.replaceFirst(key, "");
      var groupName = groupNameWithSpaces.stripLeading();
      var spaces = Strings.repeat(" ", groupNameWithSpaces.length() - groupName.length());
      output.write(key + spaces + wrap(groupName));
      output.newLine();
    }
    else if(line.equals("Objects")) {
      output.write("Objects");
      output.newLine();
      mode = Mode.Objects;
    }
    else {
      output.write(line);
      output.newLine();
    }
  }

  public void processObjects(String line) throws IOException {
    if(line.isEmpty() || line.isBlank()) {
      return;
    }
    else if(line.equals("Graphic")) {
      mode = Mode.Start;
      process(line);
    }
    else {
      output.write(wrap(line));
      output.newLine();
      mode = Mode.Object;
    }
  }

  public void processObject(String line) throws IOException {
    if(line.isEmpty() || line.isBlank()) {
      mode = Mode.Objects;
      return;
    }
    else if(line.startsWith("Relationship type  ")) {
      this.namePos = line.indexOf("Object name");
      this.typePos = line.indexOf("Object type");

      output.write(line);
      output.newLine();
      mode = Mode.Relations;
    }
    else {
      processStart(line);
    }
  }

  public static String wrap(String s) {
    s = s.replace(".", "%2E");
    s = s.replace("\"", "\\\"");
    return "\"" + s + "\"";
  }

  private String bridge(String s) {
    return s.replace(" ", "_");
  }

}
