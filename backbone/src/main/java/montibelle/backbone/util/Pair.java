package montibelle.backbone.util;

public class Pair<A, B> {

  private A first;

  private B second;

  public static<A, B> Pair<A, B> of(A first, B second) {
    return new Pair<>(first, second);
  }

  public Pair(A first, B second) {
    this.first = first;
    this.second = second;
  }

  public A getFirst() {
    return first;
  }

  public B getSecond() {
    return second;
  }

  public A getKey() {
    return first;
  }

  public B getValue() {
    return second;
  }

}
