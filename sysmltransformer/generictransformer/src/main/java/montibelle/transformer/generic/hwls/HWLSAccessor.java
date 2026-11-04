package montibelle.transformer.generic.hwls;

import de.se_rwth.commons.logging.Log;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Yaml;
import org.yaml.snakeyaml.constructor.AbstractConstruct;
import org.yaml.snakeyaml.constructor.Constructor;
import org.yaml.snakeyaml.nodes.MappingNode;
import org.yaml.snakeyaml.nodes.Node;
import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.representer.Represent;
import org.yaml.snakeyaml.representer.Representer;

import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class HWLSAccessor {

  public static final String EPILOGUE = "!Epilogue";

  public static final String PROLOGUE = "!Prologue";

  public static final String STATEMAPPING = "!Substitute";

  public static final String FILENAME = "theory";

  public static final String SESSION = "session";

  public static final String HWLS = "hwl";

  private final Path yamlFilePath;

  private final Yaml yamlWrapper;

  public HWLSAccessor(Path yamlFilePath) {
    this.yamlFilePath = yamlFilePath;

    DumperOptions dumperOptions = new DumperOptions();
    dumperOptions.setDefaultFlowStyle(DumperOptions.FlowStyle.BLOCK);

    this.yamlWrapper = new Yaml(new HwlConstructor(), new HwlRepresenter(),
        dumperOptions);
  }

  public static Tag getTagFor(HwlType type) {
    switch (type) {
      case EPILOGUE:
        return new Tag(EPILOGUE);
      case PROLOGUE:
        return new Tag(PROLOGUE);
      case SUBSTITUTE:
        return new Tag(STATEMAPPING);
      default:
        throw new IllegalArgumentException("Unknown HwlType: " + type);
    }
  }

  @SuppressWarnings("unchecked")
  public List<HwlTheory> parse(String sessionName, String filename) {
    try (FileInputStream inputStream = new FileInputStream(
        yamlFilePath.toFile())) {
      Object loaded = yamlWrapper.load(inputStream);
      List<Map<String, Object>> deserialized =
          loaded == null ?
              new ArrayList<>() :
              (List<Map<String, Object>>) loaded;

      List<HwlTheory> result = new ArrayList<>();
      for (Map<String, Object> map : deserialized) {
        if(sessionName.equals(map.get(SESSION)) && filename.equals(
            map.get(FILENAME))) {
          Object hwlsObj = map.get(HWLS);
          if(hwlsObj instanceof List) {
            result.addAll((List<HwlTheory>) hwlsObj);
          }
        }
      }
      return result;
    }
    catch (IOException e) {
      throw new RuntimeException("Could not read HWL file " + yamlFilePath, e);
    }
  }

  private static class HwlConstructor extends Constructor {

    public HwlConstructor() {
      this.yamlConstructors.put(getTagFor(HwlType.PROLOGUE), new HwlTheoryConstruct(HwlType.PROLOGUE));
      this.yamlConstructors.put(getTagFor(HwlType.EPILOGUE), new HwlTheoryConstruct(HwlType.EPILOGUE));
      this.yamlConstructors.put(getTagFor(HwlType.SUBSTITUTE), new HwlTheoryConstruct(HwlType.SUBSTITUTE));
    }

    private class HwlTheoryConstruct extends AbstractConstruct {
      private final HwlType type;

      public HwlTheoryConstruct(HwlType type) {
        this.type = type;
      }

      @Override
      public Object construct(Node node) {
        Map<Object, Object> input = HwlConstructor.this.constructMapping((MappingNode) node);

        if (!input.containsKey(FILENAME)) {
          Log.error("The HWL file is missing a \"" + FILENAME + "\" key somewhere");
        }
        if (!input.containsKey(SESSION)) {
          Log.error("The HWL file is missing a \"" + SESSION + "\" key somewhere");
        }

        return new HwlTheory(
            (String) input.get(FILENAME),
            (String) input.get(SESSION),
            type
        );
      }
    }
  }
  private static class HwlRepresenter extends Representer {

    public HwlRepresenter() {
      this.representers.put(HwlTheory.class, new RepresentHwlTheory());
    }

    private class RepresentHwlTheory implements Represent {
      @Override
      public Node representData(Object data) {
        HwlTheory value = (HwlTheory) data;
        return representMapping(
            getTagFor(value.getType()),
            Map.of(
                SESSION, value.getSessionName(),
                FILENAME, value.getFilename()
            ),
            new DumperOptions().getDefaultFlowStyle()
        );
      }
    }
  }
}
