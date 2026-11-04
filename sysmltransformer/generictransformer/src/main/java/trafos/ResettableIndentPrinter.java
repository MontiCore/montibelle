package trafos;


import de.monticore.prettyprint.IndentPrinter;

public class ResettableIndentPrinter extends IndentPrinter {

  private IndentPrinter printer;

  public ResettableIndentPrinter() {
    this.printer = new IndentPrinter();
  }

  public ResettableIndentPrinter(IndentPrinter printer) {
    this.printer = printer;
  }

  public IndentPrinter getPrinter() {
    return printer;
  }

  public void setPrinter(IndentPrinter printer) {
    this.printer = printer;
  }

  public void reset() {
    this.printer = new IndentPrinter();
  }

  @Override
  public void print(Object o) {
    printer.print(o);
  }

  @Override
  public String getContent() {
    return printer.getContent();
  }
}
