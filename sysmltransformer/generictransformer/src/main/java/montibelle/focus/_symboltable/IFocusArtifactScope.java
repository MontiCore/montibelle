package montibelle.focus._symboltable;

import de.monticore.symboltable.ISymbol;
import montibelle.focus._ast.ASTFocusElement;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

public interface IFocusArtifactScope extends IFocusArtifactScopeTOP {

  @Override
  default Optional<ISymbol> getTopLevelSymbol() {
    List<ISymbol> topSymbolList = new ArrayList<>();
    topSymbolList.addAll(getStateSpaceSymbols().values());
    topSymbolList.addAll(getAutomatonSymbols().values());
    topSymbolList.addAll(getEventAutomatonSymbols().values());
    topSymbolList.addAll(getTheorySymbols().values());
    topSymbolList.addAll(getDatatypesSymbols().values());
    topSymbolList.addAll(getEnumTypeSymbols().values());
    topSymbolList.addAll(getUserDefinedStructSymbols().values());
    topSymbolList.addAll(getFieldSymbols().values());
    topSymbolList.addAll(getDataIncSymbols().values());
    topSymbolList.addAll(getSessionSymbols().values());
    topSymbolList.addAll(getSpsSymbols().values());
    topSymbolList.addAll(getBundleSymbols().values());
    topSymbolList.addAll(getChannelSymbols().values());
    topSymbolList.addAll(getChannelTypeSymbols().values());
    topSymbolList.addAll(getParameterSymbols().values());
    topSymbolList.addAll(getSpecificationSymbols().values());
    topSymbolList.addAll(getRefinementSymbols().values());
    topSymbolList.addAll(getCompositionSymbols().values());
    topSymbolList.addAll(getConnectorsSymbols().values());
    topSymbolList.addAll(getChannelMappingSymbols().values());
    topSymbolList.addAll(getInstanceSymbols().values());
    topSymbolList.addAll(getParameterValueSymbols().values());
    topSymbolList.addAll(getElementSymbols().values());
    topSymbolList.addAll(getTimingSymbols().values());
    topSymbolList.addAll(getDiagramSymbols().values());
    topSymbolList.addAll(getTypeSymbols().values());
    topSymbolList.addAll(getTypeVarSymbols().values());
    topSymbolList.addAll(getVariableSymbols().values());
    topSymbolList.addAll(getFunctionSymbols().values());
    topSymbolList.addAll(getRequirementSymbols().values());
    topSymbolList.addAll(getFocusFunctionSymbols().values());

    if (topSymbolList.size() == 1) {
      return Optional.of(topSymbolList.get(0));
    } else {
      List<ISymbol> focusElements = new ArrayList<>();
      for (ISymbol symbol : topSymbolList) {
        if (symbol.getAstNode() instanceof ASTFocusElement) {
          focusElements.add(symbol);
        }
      }

      if (focusElements.size() == 1) {
        return Optional.of(focusElements.get(0));
      }
    }

    return Optional.empty();
  }
}
