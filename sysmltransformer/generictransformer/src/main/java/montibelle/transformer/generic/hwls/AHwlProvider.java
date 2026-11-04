package montibelle.transformer.generic.hwls;

import java.util.List;
import java.util.stream.Collectors;

public abstract class AHwlProvider {

  public abstract List<HwlTheory> getHwls(String session, String filename);

  public List<String> getProloguesSessionsFor(String session, String filename) {
    return getHwls(session, filename).stream()
        .filter(it -> it.getType() == HwlType.PROLOGUE)
        .map(HwlTheory::getSessionName)
        .collect(Collectors.toList());
  }

  public List<String> getEpilogueSessionsFor(String session, String filename) {
    return getHwls(session, filename).stream()
        .filter(it -> it.getType() == HwlType.EPILOGUE)
        .map(HwlTheory::getSessionName)
        .collect(Collectors.toList());
  }

  public List<String> getPrologueImportsFor(String session, String filename) {
    return getHwls(session, filename).stream()
        .filter(it -> it.getType() == HwlType.PROLOGUE)
        .map(it -> it.importFrom(session))
        .collect(Collectors.toList());
  }

  public List<String> getEpilogueImportsFor(String session, String filename) {
    return getHwls(session, filename).stream()
        .filter(it -> it.getType() == HwlType.EPILOGUE)
        .map(it -> it.importFrom(session))
        .collect(Collectors.toList());
  }

  public HwlTheory substituteFor(String session, String filename) {
    return getHwls(session, filename).stream()
        .filter(it -> it.getType() == HwlType.SUBSTITUTE)
        .findFirst()
        .orElse(null);
  }
}
