package montibelle.focus._symboltable;

public class ChannelTypeSymbol extends ChannelTypeSymbolTOP
    implements Comparable<ChannelTypeSymbol> {

  public ChannelTypeSymbol(String name) {
    super(name);
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof ChannelTypeSymbol &&
        name.equals(((ChannelTypeSymbol) other).name);
  }

  @Override
  public int hashCode() {
    return name.hashCode();
  }

  @Override
  public int compareTo(ChannelTypeSymbol other) {
    return name.compareTo(other.name);
  }
}
