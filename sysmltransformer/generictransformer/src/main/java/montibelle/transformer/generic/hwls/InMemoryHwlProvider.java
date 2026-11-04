package montibelle.transformer.generic.hwls;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class InMemoryHwlProvider extends AHwlProvider {

  private final Map<String, Map<String, List<HwlTheory>>> hwls = new HashMap<>();

  public Map<String, Map<String, List<HwlTheory>>> getHwlsMap() {
    return hwls;
  }

  @Override
  public List<HwlTheory> getHwls(String session, String filename) {
    return hwls
        .getOrDefault(session, new HashMap<>())
        .getOrDefault(filename, List.of());
  }

  public void addHwl(String sessionName, String filename, HwlTheory hwl) {
    Map<String, List<HwlTheory>> session = hwls.get(sessionName);
    if (session != null) {
      List<HwlTheory> theory = session.get(filename);
      if (theory != null && !theory.isEmpty()) {
        theory.add(hwl);
      } else {
        List<HwlTheory> list = new ArrayList<>();
        list.add(hwl);
        session.put(filename, list);
      }
    } else {
      Map<String, List<HwlTheory>> theoryMap = new HashMap<>();
      List<HwlTheory> list = new ArrayList<>();
      list.add(hwl);
      theoryMap.put(filename, list);
      hwls.put(sessionName, theoryMap);
    }
  }
}
