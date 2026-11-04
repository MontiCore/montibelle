import de.monticore.lang.componentconnector.ComponentConnectorMill;
import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol;
import de.monticore.symbols.compsymbols._symboltable.PortSymbol;
import de.monticore.symbols.compsymbols._visitor.CompSymbolsVisitor2;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import de.se_rwth.commons.logging.Log;
import focus.SymType2MCTypePrinter;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTChannelTypeBuilder;
import montibelle.focus._symboltable.ChannelTypeSymbol;
import trafos.ITypePrinter;
import trafos.SourceMap;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

public class ChannelFunctions implements CompSymbolsVisitor2 {

  private ChannelFunctions() {}

  private MildComponentSymbol component;

  private ITypePrinter typePrinter;

  private List<ChannelTypeSymbol> chanTypes;

  public static List<ChannelTypeSymbol> createChanType(
      MildComponentSymbol component, ITypePrinter typePrinter
  ) {
    var visitor = new ChannelFunctions();
    visitor.component = component;
    visitor.typePrinter = typePrinter;
    visitor.chanTypes = new ArrayList<>();
    var traverser = ComponentConnectorMill.inheritanceTraverser();
    traverser.add4CompSymbols(visitor);
    component.getPorts().stream().forEach(p -> p.accept(traverser));
    return new ArrayList<>(new HashSet<>(visitor.chanTypes));
  }

  @Override
  public void visit(PortSymbol port) {
    var typeName = typePrinter.print(port.getType());
    var timing = SourceMap.mapToFocus(port.getTiming()).getName();
    ASTMCType mcType;
    try {
      mcType = FocusMill.parser().parse_StringMCType(
          new SymType2MCTypePrinter().print(port.getType())).get();
    }
    catch (IOException e) {
      throw new RuntimeException(e);
    }

    var chanType = new ASTChannelTypeBuilder()
        .setName(typeName.replaceAll("[^A-Za-z0-9]", "") + timing)
        .setTiming(timing)
        .setMCType(mcType)
        .build();

    var tool = new FocusTool();
    tool.createSymbolTable(chanType);
    tool.completeSymbolTable(chanType);

    if(chanType.isPresentSymbol()) {
      chanTypes.add(chanType.getSymbol());
    }
    else {
      Log.warn(String.format("Channel type symbol %s could not be created", typeName));
    }
  }
}
