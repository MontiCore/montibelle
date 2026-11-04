package montibelle.transformer.sysml;

import java.util.HashMap;
import java.util.Map;

public final class Constants {

  private Constants() {
  }

  public static final char SEP = '_';

  public static final Map<String, String> BASIC_TYPES = new HashMap<>();

  static {
    BASIC_TYPES.put("boolean", "bool");
    BASIC_TYPES.put("Boolean", "bool");
    BASIC_TYPES.put("ScalarValues.Boolean", "bool");
    BASIC_TYPES.put("int", "int");
    BASIC_TYPES.put("Integer", "int");
    BASIC_TYPES.put("ScalarValues.Integer", "int");
    BASIC_TYPES.put("nat", "nat");
    BASIC_TYPES.put("Natural", "nat");
    BASIC_TYPES.put("ScalarValues.Natural", "nat");
    BASIC_TYPES.put("String", "string");
    BASIC_TYPES.put("ScalarValues.String", "string");
  }
}
