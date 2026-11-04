package trafos;

import de.monticore.lang.sysmlparts._ast.ASTEndpoint;
import de.monticore.lang.sysmlparts._ast.ASTConnectionUsage;
import de.monticore.lang.sysmlparts._symboltable.AttributeUsageSymbol;
import de.monticore.lang.sysmlparts._symboltable.ISysMLPartsScope;
import de.monticore.lang.sysmlparts._symboltable.PortUsageSymbol;
import de.monticore.lang.sysmlparts._visitor.SysMLPartsVisitor2;
import de.monticore.lang.sysmlv2.symboltable.adapters.AttributeUsage2PortSymbolAdapter;
import de.monticore.symbols.compsymbols._symboltable.PortSymbol;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class ConnectionMapping implements SysMLPartsVisitor2 {


  private static final Map<AttributeUsageSymbol, String> conversion = new HashMap<>();

  private static final ConnectionMapping INSTANCE = new ConnectionMapping();

  private ConnectionMapping() {
  }

  public static ConnectionMapping getInstance() {
    return INSTANCE;
  }

  public void visit(ASTConnectionUsage node) {
    if(node.isPresentSrc() && node.isPresentTgt()) {
      ISysMLPartsScope scope = node.getEnclosingScope();
      ASTEndpoint src = node.getSrc();
      ASTEndpoint tgt = node.getTgt();

      Optional<AttributeUsageSymbol> potAttr = scope.resolveAttributeUsage(
          src.getMCQualifiedName().getQName());
      Optional<PortUsageSymbol> potPort = scope.resolvePortUsage(
          tgt.getMCQualifiedName().getQName());
      if(potAttr.isPresent() && potPort.isPresent()) {
        PortSymbol portSymbol = getPortSymbol(potPort.get());
        String pattern = calculatePattern(portSymbol);
        conversion.put(potAttr.get(), pattern);
        return;
      }
      potAttr = scope.resolveAttributeUsage(
          tgt.getMCQualifiedName().getQName());
      potPort = scope.resolvePortUsage(src.getMCQualifiedName().getQName());
      if(potAttr.isPresent() && potPort.isPresent()) {
        PortSymbol portSymbol = getPortSymbol(potPort.get());
        String pattern = calculatePattern(portSymbol);
        conversion.put(potAttr.get(), pattern);
        return;
      }
    }
  }

  public PortSymbol getPortSymbol(PortUsageSymbol pu) {
    var ins = pu.getInputAttributes().stream()
        .map(au -> new AttributeUsage2PortSymbolAdapter(au, pu, true)
        );
    var outs = pu.getOutputAttributes().stream()
        .map(au -> new AttributeUsage2PortSymbolAdapter(au, pu, false)
        );
    List<PortSymbol> portSymbols = Stream.concat(ins, outs).collect(
        Collectors.toList());
    return portSymbols.get(0);
  }

  public String calculatePattern(PortSymbol ps) {
    return "channel_" + ps.getName().replace('.', '_') + "_pattern";
  }

  public boolean isConnectedToPort(AttributeUsageSymbol attr) {
    return conversion.containsKey(attr);
  }

  public String getPattern(AttributeUsageSymbol attr) {
    return conversion.get(attr);
  }
}

