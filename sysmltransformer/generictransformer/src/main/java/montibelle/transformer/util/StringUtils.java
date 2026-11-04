package montibelle.transformer.util;

public class StringUtils {
  public static String toAlphanumeric(String input) {
    if (input == null) {
      return null;
    }
    return input.replaceAll("[^A-Za-z0-9 ]", "");
  }
}
