package montibelle.backbone.util;

import com.fasterxml.jackson.annotation.JsonAutoDetect;
import com.fasterxml.jackson.annotation.PropertyAccessor;
import com.fasterxml.jackson.databind.JavaType;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.dataformat.yaml.YAMLFactory;
import de.se_rwth.commons.logging.Log;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class YamlUtil<T> {

  private Class<T> targetClass;

  private ObjectMapper mapper = new ObjectMapper(new YAMLFactory());

  public YamlUtil(Class<T> targetClass) {
    this.targetClass = targetClass;
    mapper.setVisibility(mapper.getSerializationConfig().getDefaultVisibilityChecker()
        .withFieldVisibility(JsonAutoDetect.Visibility.ANY)
        .withGetterVisibility(JsonAutoDetect.Visibility.NONE)
        .withSetterVisibility(JsonAutoDetect.Visibility.NONE)
        .withCreatorVisibility(JsonAutoDetect.Visibility.NONE));
    mapper.setVisibility(PropertyAccessor.FIELD, JsonAutoDetect.Visibility.ANY);
    mapper.findAndRegisterModules();
  }

  public void writeToYaml(String path, T t) throws IOException {
    writeToYaml(path, Collections.singletonList(t));
  }

  public void writeToYaml(String path, List<T> list) throws IOException {
    Log.debug("Writing to " + path, getClass().getName());
    mapper.writeValue(new File(path), list);
  }

  public List<T> readFromYaml(String path) throws IOException {
    File file = new File(path);
    if (!file.exists()) {
      return new ArrayList<>();
    }
    Log.debug("Reading from " + path, getClass().getName());
    JavaType targetType = mapper.getTypeFactory()
        .constructCollectionType(ArrayList.class, targetClass);
    return mapper.readValue(file, targetType);
  }

  public void appendToYaml(String path, T t) throws IOException {
    List<T> list = readFromYaml(path);
    list.add(t);
    writeToYaml(path, list);
  }

  public void removeFromYaml(String path, T t) throws IOException {
    List<T> list = readFromYaml(path);
    list.remove(t);
    writeToYaml(path, list);
  }

  public void saveObjectInYaml(String path, T t) throws IOException {
    File file = new File(path);
    if (!file.exists()) {
      file.getParentFile().mkdirs();
      file.createNewFile();
      writeToYaml(path, t);
    }
    else {
      appendToYaml(path, t);
    }
  }

}
