import de.se_rwth.commons.logging.Log
import extension.comparator.FileCompare
import montibelle.focus.FocusMill
import montibelle.focus.FocusTool
import montibelle.focus._ast.ASTRefinement
import montibelle.focus._ast.ASTRefinementBuilder
import montibelle.focus._ast.ASTSessionBuilder
import montibelle.focus._ast.ASTStateSpaceBuilder
import montibelle.focus._ast.ASTStateVariableBuilder
import montibelle.focus._ast.ASTTheoryBuilder
import montibelle.focus._symboltable.StateSpaceSymbol
import montibelle.transformer.generic.Constants
import montibelle.transformer.util.FreemarkerInterface
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.io.StringWriter
import java.nio.file.Files
import java.nio.file.Paths

class StatemapTest {

  @BeforeEach
  fun setUp() {
    Log.init()
    FocusMill.reset()
    FocusMill.init()
    FocusMill.globalScope().clear()
  }

  companion object {
    const val BASE = "src/test/resources/montibelle/transformer/generic/"
    const val StateMap = "ref_EventAutomata.thy"
  }

  @FileCompare(base = BASE, value = [StateMap])
  @Test
  fun testMappingForSameStatespace() {
    val tool = FocusTool()
    tool.init()

    val stateAst = ASTStateSpaceBuilder()
      .setName("RefinedAutomaton.States")
      .setStatesList(listOf("S1", "S2"))
      .uncheckedBuild()

    val spsSession = ASTSessionBuilder()
      .setName("sps")
      .setPathList(listOf())
      .build()

    val stateTheory = ASTTheoryBuilder()
      .setSessionName("sps")
      .setFilename("def_${stateAst.name.replace('.', '_')}")
      .build()
    stateAst.theory = stateTheory.name

    val variable = ASTStateVariableBuilder()
      .setName("attr")
      .setPattern("attr")
      .setMCType(FocusMill.parser().parse_StringMCType("boolean").orElseThrow())
      .build()
    stateAst.setStateVariableList(listOf(variable))

    tool.createSymbolTable(spsSession)
    tool.createSymbolTable(stateTheory)

    val stateSpaceSym = StateSpaceSymbol(stateAst.name)
    stateSpaceSym.setVariableNamesList(stateAst.statesList)
    stateSpaceSym.setTheory(stateTheory.name)
    stateSpaceSym.setAstNode(stateAst)
    FocusMill.globalScope().add(stateSpaceSym)

    val inputBundle = FocusMill.bundleSymbolBuilder()
      .setName("InputBundle")
      .setTheory(stateTheory.name)
      .build()
    val outputBundle = FocusMill.bundleSymbolBuilder()
      .setName("OutputBundle")
      .setTheory(stateTheory.name)
      .build()
    FocusMill.globalScope().add(inputBundle)
    FocusMill.globalScope().add(outputBundle)

    val refinedSym = FocusMill.eventAutomatonSymbolBuilder()
      .setName("RefinedAutomaton")
      .setTheory(stateTheory.name)
      .setStatespaceName(stateAst.name)
      .setInputName("InputBundle")
      .setOutputName("OutputBundle")
      .build()
    FocusMill.globalScope().add(refinedSym)

    val roughSym = FocusMill.eventAutomatonSymbolBuilder()
      .setName("RoughAutomaton")
      .setTheory(stateTheory.name)
      .setStatespaceName(stateAst.name)
      .setInputName("InputBundle")
      .setOutputName("OutputBundle")
      .build()
    FocusMill.globalScope().add(roughSym)

    val refinement: ASTRefinement = ASTRefinementBuilder()
      .setName("R1")
      .setRoughName("RoughAutomaton")
      .setRefinedName("RefinedAutomaton")
      .setTheory(stateTheory.name)
      .build()

    tool.createSymbolTable(refinement)
    tool.completeSymbolTable(refinement)
    tool.completeSymbolTable(stateTheory)

    val writer = StringWriter()
    FreemarkerInterface.instance.generate(
      Constants.EVENTAUT_REF,
      writer,
      false,
      stateTheory,
      refinement
    )

    val refFile = Paths.get("src/test/resources/montibelle/transformer/generic/ref_EventAutomata.thy")
    Files.createDirectories(refFile.parent)
    Files.writeString(refFile, writer.toString())
  }
}
