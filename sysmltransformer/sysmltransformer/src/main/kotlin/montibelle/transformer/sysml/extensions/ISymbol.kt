package montibelle.transformer.sysml.extensions

import de.monticore.lang.sysmlv2._symboltable.ISysMLv2ArtifactScope
import de.monticore.symboltable.ISymbol

fun ISymbol.getPackageNameFromScope(): List<String> {
  val accu = mutableListOf<String>()
  var scope = this.enclosingScope
  while (scope != null && scope !is ISysMLv2ArtifactScope) {
    if (scope.isPresentName) {
      accu.add(0,scope.name)
    }
    scope = scope.enclosingScope
  }
  return accu
}
