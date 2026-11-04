package montibelle.focus._ast;

import com.google.common.collect.Lists;
import de.se_rwth.commons.Names;
import de.se_rwth.commons.Splitters;
import montibelle.focus._symboltable.ChannelSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class ASTBundle extends ASTBundleTOP {

  @Override
  public List<ChannelSymbol> getChannels() {
    return getChannelsList().stream()
        .map(n->getEnclosingScope().resolveChannel(n).get())
        .collect(Collectors.toList());
  }

  public String getSimpleName() {
    return Names.getSimpleName(getName());
  }

  public List<String> getPackage() {
    var qualifier = Names.getQualifier(getName());
    if(qualifier.isEmpty()) {
      return new ArrayList<>();
    }
    return Lists.newArrayList(Splitters.DOT.split(qualifier));
  }

  public  boolean isEventBased() {
    return getTimingSymbol().isEventBased();
  }

  public boolean isTimeSyncronous() {
    return getTimingSymbol().isTimeSyncronous();
  }

  public boolean isStrictlyTimeSyncronous() {
    return getTimingSymbol().isStrictlyTimeSyncronous();
  }
}
