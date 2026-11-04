package montibelle.focus._ast;

public class ASTChannel extends ASTChannelTOP implements Comparable<ASTChannel> {

  private int cardinality;

  public ASTChannel() {
    pattern = localName + "_pattern";
    cardinality = 1;
  }

  public void setCardinality(int c) {
    this.cardinality = c;
  }

  public int getCardinality() {
    return cardinality;
  }

  @Override
  public int compareTo(ASTChannel other) {
    return localName.compareTo(other.localName);
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof ASTChannel
        && localName.equals(((ASTChannel)other).localName);
  }

  @Override
  public int hashCode() {
    return name.hashCode();
  }

  @Override
  public String toString() {
    return name;
  }

}
