package montibelle.focus._symboltable;

public class ChannelSymbol extends ChannelSymbolTOP implements Comparable<ChannelSymbol> {

  public ChannelSymbol(String name) {
    super(name);
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof ChannelSymbol &&
        name.equals(((ChannelSymbol)other).name);
  }

  @Override
  public int hashCode() {
    return name.hashCode();
  }

  @Override
  public int compareTo(ChannelSymbol other) {
     return name.compareTo(other.name);
  }
}
