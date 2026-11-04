package montibelle.focus

import FocusCompleter
import de.monticore.io.paths.MCPath
import de.monticore.lang.sysmlv2.SysMLv2MillTOP
import de.monticore.ocl.types3.OCLSymTypeRelations
import de.monticore.symbols.basicsymbols.BasicSymbolsMill
import de.monticore.symboltable.modifiers.AccessModifier
import de.monticore.types.mccollectiontypes.types3.MCCollectionSymTypeRelations
import de.monticore.types3.TypeCheck3
import de.monticore.types3.TypeCheck3Access
import focus.FocusTypeCheck3
import montibelle.focus._ast.*
import montibelle.focus._symboltable.*
import montibelle.focus._visitor.FocusTraverser
import montibelle.transformer.generic.Constants
import montibelle.transformer.generic.Constants.CODE_PRFX
import montibelle.transformer.generic.Constants.SEP
import java.nio.file.Path

class FocusTool: FocusToolTOP() {
  companion object {
    @get:JvmStatic
    var previousTypecheck: TypeCheck3? = null
      private set
  }

  fun storeSymbols(scope: IFocusArtifactScope, directory: Path, fileName: String) {
    val encodedFileName = FocusGlobalScope.encodeSymbolName(fileName)
    super.storeSymbols(scope, directory.resolve(encodedFileName).toString())
  }

  override fun init() {
    previousTypecheck = TypeCheck3Access.currentDelegate()
    FocusMill.init()
    BasicSymbolsMill.initializePrimitives()
    BasicSymbolsMill.initializeString()
    FocusTypeCheck3.init()
    val gs = FocusMill.globalScope()

    if (gs.resolveType("List").isEmpty) {
      gs.add(
        BasicSymbolsMill.typeSymbolBuilder()
          .setName("List")
          .setSpannedScope(BasicSymbolsMill.scope())
          .build()
      )
    }

    if (gs.resolveType("nat").isEmpty) {
      gs.add(
        BasicSymbolsMill.typeSymbolBuilder()
          .setName("nat")
          .setSpannedScope(BasicSymbolsMill.scope())
          .build()
      )
    }

    MCCollectionSymTypeRelations.init()
    OCLSymTypeRelations.init()
  }

  override fun completeSymbolTable(node: ASTFocusElement) {
    val traverser: FocusTraverser = FocusMill.inheritanceTraverser()
    traverser.add4Focus(FocusCompleter())
    node.accept(traverser)
  }

  fun setup(target: Path) {
    val gs = FocusMill.globalScope()

    gs.fileExt = ".sym"

    gs.symbolPath = MCPath(
      target.toFile().walk()
        .filter { it.isDirectory }
        .map { it.toPath() }
        .toList()
    )
    if (gs.resolveTiming("EVENT").isEmpty) {
      val timing = TimingSymbolBuilder()
        .setName("EVENT")
        .setEnclosingScope(gs)
        .build()

      val timingAST = ASTEventTimingBuilder().build()

      timingAST.symbol = timing
      timingAST.enclosingScope = gs
      timing.astNode = timingAST

      gs.add(timing)
    }

    if (gs.resolveTiming("SYNC").isEmpty) {
      val timing = TimingSymbolBuilder()
        .setName("SYNC")
        .setEnclosingScope(gs)
        .build()

      val timingAST = ASTSyncronousTimingBuilder().build()

      timingAST.symbol = timing
      timingAST.enclosingScope = gs
      timing.astNode = timingAST

      gs.add(timing)
    }
  }

  fun clone(
    node: ASTEventAutomaton,
    inputBundleName: String,
    outputBundleName: String) : ASTEventAutomaton
  {
    val statesClone = ASTStateSpaceBuilder()
      .setName(node.states.name + "_clone")
      .setStatesList(node.states.statesList)
      .setStateVariablesList(node.states.stateVariableList)
      .uncheckedBuild()

    return ASTEventAutomatonBuilder()
      .setFqn(Constants.CODE_PRFX + "." + node.name)
      .setStrongCausal(node.isStrongCausal)
      .setEventTransitionsList(node.eventTransitionList)
      .setTickTransitionsList(node.tickTransitionsList)
      .setInitialList(node.initialList)
      .setParametersList(node.parameterList)
      .setInputBundle(inputBundleName)
      .setOutputBundle(outputBundleName)
      .setStates(statesClone)
      .uncheckedBuild()
  }

  fun buildCodeTheoryAndSessionFor(symbol: BundleSymbol): Pair<ASTTheory, ASTSession>
  {
    val `package` = symbol.name.split(".").dropLast(1)
    val session = ASTSessionBuilder()
      .setName(CODE_PRFX + "_" + `package`.joinToString(SEP.toString()))
      .setPathList(listOf(CODE_PRFX) + `package`)
      .build()
    session.parent = "sps"
    session.addGroup("code")

    val theory: ASTTheory = ASTTheoryBuilder()
      .setSessionName(session.name)
      .setFilename("$CODE_PRFX$SEP${symbol.name.replace('.', SEP)}")
      .build()
    symbol.codeTheory = theory.name

    return Pair(theory, session)
  }

  fun buildCodeTheoryAndSessionFor(node: ASTIAutomaton): Pair<ASTTheory, ASTSession>
  {
    val session = ASTSessionBuilder()
      .setName(CODE_PRFX + node.`package`.map { "_" + it }.joinToString() + "_" + node.name)
      .setPathList(listOf(CODE_PRFX) + node.`package` + node.name)
      .build()
    session.parent = "component"
    session.addGroup("code")

    val theory: ASTTheory = ASTTheoryBuilder()
      .setSessionName(session.name)
      .setFilename("$CODE_PRFX$SEP${node.name.replace('.', SEP)}")
      .build()
    node.codeTheory = theory.name

    return Pair(theory, session)
  }

}
