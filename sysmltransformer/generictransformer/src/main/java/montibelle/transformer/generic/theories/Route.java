package montibelle.transformer.generic.theories;

public class Route implements IRoute {

  private final Element raw;

  private final Binding fin;

  public Route(Element raw, Binding fin) {
    this.raw = raw;
    this.fin = fin;
  }

  @Override
  public Element getRaw() {
    return raw;
  }

  @Override
  public Binding getFinal() {
    return fin;
  }

}
