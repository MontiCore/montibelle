package montibelle.transformer.sysml

import CalcDefTransformer
import ChannelFunctions
import RequirementHelper.*
import cc2focus.Requirement2FocusRequirementPrinter
import de.monticore.expressions.expressionsbasis._ast.ASTExpression
import de.monticore.expressions.expressionsbasis._visitor.ExpressionsBasisVisitor2
import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol
import de.monticore.lang.componentconnector._symboltable.MildInstanceSymbol
import de.monticore.lang.sysmlactions._ast.ASTCalcDef
import de.monticore.lang.sysmlactions._visitor.SysMLActionsVisitor2
import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.monticore.lang.sysmlv2.SysMLv2Tool
import de.monticore.lang.sysmlv2._visitor.SysMLv2Traverser
import de.monticore.literals.mccommonliterals._visitor.MCCommonLiteralsVisitor2
import de.monticore.prettyprint.IndentPrinter
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol
import de.monticore.symbols.compsymbols._symboltable.Timing
import de.monticore.symboltable.serialization.JsonPrinter
import de.monticore.types3.TypeCheck3
import de.se_rwth.commons.logging.Log
import focus.Bundles
import focus.Refinement
import focus.Sps
import montibelle.focus.*
import montibelle.focus._ast.ASTBundle
import montibelle.focus._ast.ASTRequirement
import montibelle.focus._ast.ASTRequirementBuilder
import montibelle.focus._symboltable.IAutomatonSymbol
import montibelle.focus._symboltable.IFocusArtifactScope
import montibelle.transformer.generic.Constants.*
import montibelle.transformer.generic.hwls.AHwlProvider
import montibelle.transformer.generic.hwls.FilebasedHwlProvider
import montibelle.transformer.generic.hwls.InMemoryHwlProvider
import montibelle.transformer.generic.sessions.SessionGenerator
import montibelle.transformer.sysml.printer.*
import montibelle.transformer.util.FreemarkerInterface
import org.apache.commons.cli.*
import trafos.ConnectionMapping
import trafos.IExpressionPrinter
import trafos.ResettableIndentPrinter
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*
import java.util.stream.Collectors
import kotlin.collections.plusAssign
import kotlin.io.path.extension
import kotlin.io.path.isDirectory

object Main {

  @JvmStatic
  fun info(str: String) {
    Log.info(str, "")
  }

  @JvmStatic
  fun ifAnyThenInfo(lst: List<Any>, found: String, cont: String) {
    if(lst.isEmpty() && found.isNotEmpty()) {
      info(found.replace("#", lst.size.toString()))

    }
    else if (lst.isNotEmpty()) {
      info(found.replace("#", lst.size.toString())
          + cont.replace("#", lst.size.toString()))
    }
  }

  @JvmStatic
  fun main(args: Array<String>) {
    val options = Options()
      .addOption(Option.builder("s").hasArgs().valueSeparator(';').desc("source").build())
      .addOption("t", "target", true, "target")
      .addOption("c", "comment", false, "de-activate comment")
      .addOption("h", "help", false, "help")
      .addOption("hwl", true, "path to yaml file containing hwl declarations")
      .addOption("v", false, "verbosity level: info")
      .addOption("vv", false, "verbosity level: debug")

    val cmd: CommandLine = try {
      DefaultParser().parse(options, args)
    } catch (ex: ParseException) {
      HelpFormatter().printHelp("java -jar <JAR-Name>", options)
      return
    }

    if (cmd.hasOption("h")) {
      HelpFormatter().printHelp("java -jar <JAR-Name>", options)
      return
    }

    if (!cmd.hasOption("v") && cmd.hasOption("vv")) {
      Log.initDEBUG()
    } else if (cmd.hasOption("v") && !cmd.hasOption("vv")) {
      Log.init()
    } else {
      Log.initWARN()
    }
    Log.getFindings().clear()

    val versionStream = this::class.java.getResourceAsStream("/version.properties")
    if (versionStream != null) {
      val props = Properties()
      props.load(versionStream)

      info("This is sysmltransformer " + props.getProperty("version"))
    } else {
      Log.warn("Symsmltransformer version not found.")
    }

    val sources = if (cmd.hasOption("s")) {
      listOf(*cmd.getOptionValues("s")).map { Paths.get(it) }
    } else {
      listOf(Paths.get("."))
    }
    val sourceFiles = mutableListOf<Path>()
    for(source in sources) {
      if (source.isDirectory()) {
        val models = Files.walk(source)
          .filter { it.extension == "sysml" }
          .collect(Collectors.toList())
        sourceFiles.addAll(models)
      }
      else {
        sourceFiles.add(source)
      }
    }

    val target = if (cmd.hasOption("t")) Paths.get(cmd.getOptionValue("t")) else Paths.get("target")

    val hwlProvider = if (cmd.hasOption("hwl")) {
      FilebasedHwlProvider(Paths.get(cmd.getOptionValue("hwl")))
    } else {
      InMemoryHwlProvider()
    }

    JsonPrinter.enableIndentation()

    transformIncrementally(sourceFiles, target, hwlProvider, !cmd.hasOption("c"))
  }

  private val sysmlSymbolDir = "sysmlSymbols"

  @JvmStatic
  fun transformIncrementally(
    sources: List<Path>,
    target: Path,
    hwlProvider: AHwlProvider,
    comment: Boolean)
  {
    val sysmlTool = SysMLv2Tool()
    sysmlTool.init()

    target.resolve(sysmlSymbolDir)
      .toFile()
      .walk()
      .filter { it.isDirectory }
      .map { it.toPath() }
      .forEach { path ->
          sysmlTool.globalScope.symbolPath.addEntry(path)
      }

    info("Processing ${sources.map { it.fileName }}")

    val asts = sources.map { sysmlTool.parse(it.toString()) }
    info("✅ Parsed successfully")

    val artifacts = asts.map { sysmlTool.createSymbolTable(it) }
    asts.forEach { sysmlTool.completeSymbolTable(it) }
    asts.forEach { sysmlTool.finalizeSymbolTable(it) }
    info("✅ Symboltable created")

    asts.forEach { sysmlTool.runDefaultCoCos(it) }
    asts.forEach { sysmlTool.runAdditionalCoCos(it) }
    info("✅ CoCos passed")

    info("\uD83D\uDCBE Storing SysMLv2 symbols of ${artifacts.size} artifact scope(s)")
    artifacts.forEach {
      sysmlTool.storeSymbols(it, target.resolve(sysmlSymbolDir).resolve("${it.name}.sym").toString())
    }

    val expressionPrinter = getEventExpressionPrinter(sysmlTool.inheritanceTraverser)

    info("\uD83D\uDD0E Searching for part defs / components")
    val components = artifacts.flatMap { SysMLProvider.provideComponents(it) }
    ifAnyThenInfo(components, "", "Found # part defs / components")

    info("\uD83D\uDD0E Searching for user-defined types")
    val userTypes = artifacts.flatMap { SysMLProvider.provideUserDefinedTypes(it) }
    ifAnyThenInfo(userTypes, "", "Found # user-defined type(s)")

    info("\uD83D\uDD0E Searching for requirements")
    val requirements = artifacts.flatMap { SysMLProvider.provideRequirements(it) }
    ifAnyThenInfo(requirements, "", "Found # requirement(s)")

    val calcDefs = mutableListOf<String>()

    val calcDefTraverser = SysMLv2Mill.traverser()
    calcDefTraverser.add4SysMLActions(object : SysMLActionsVisitor2 {
      override fun visit(node: ASTCalcDef) {
        if(node.isPresentExpression()) {
          calcDefs.add(CalcDefTransformer.transform(node))
        }
      }
    })

    asts.forEach { it.accept(calcDefTraverser) }

    val channels = mutableListOf<String>()
    val bundles = mutableListOf<String>()
    components.forEach { component ->
      if (component.refinementStart.orElse(null)?.fullName == component.fullName) {
        component.ports.forEach { port ->
          val name = trafos.SourceMap.mapToFocus(port)
          val localName = "channel_${port.name.replace('.', '_')}"
          val timing = when (port.timing) {
            Timing.UNTIMED -> "TONE"
            Timing.TIMED_SYNC -> "SYNC"
            Timing.TIMED, null -> "EVENT"
          }
          val type = TypePrinter().print(port.type)
            .replace(Regex("[^A-Za-z0-9]"), "") + timing
          channels += "$name $localName $type ${localName}_pattern"
        }

        val inputPorts = component.ports.filter { it.isIncoming }
        val inputTiming = when (inputPorts.lastOrNull()?.timing) {
          Timing.UNTIMED -> "TONE"
          Timing.TIMED_SYNC -> "SYNC"
          Timing.TIMED, null -> "EVENT"
        }
        bundles += inputPorts.sortedBy { trafos.SourceMap.mapToFocus(it) }.joinToString(
          separator = " ",
          prefix = "bundle \"${component.fullName}.Input\" { channels ",
          postfix = "; timing $inputTiming; theory def_${component.fullName.replace('.', '_')}_Input; }"
        ) { port -> trafos.SourceMap.mapToFocus(port) }

        val outputPorts = component.ports.filter { it.isOutgoing }
        val outputTiming = when (outputPorts.lastOrNull()?.timing) {
          Timing.UNTIMED -> "TONE"
          Timing.TIMED_SYNC -> "SYNC"
          Timing.TIMED, null -> "EVENT"
        }
        bundles += outputPorts.sortedBy { trafos.SourceMap.mapToFocus(it) }.joinToString(
          separator = " ",
          prefix = "bundle \"${component.fullName}.Output\" { channels ",
          postfix = "; timing $outputTiming; theory def_${component.fullName.replace('.', '_')}_Output; }"
        ) { port -> trafos.SourceMap.mapToFocus(port) }

        info("Created bundles for ${component.fullName}")
      }
    }

    val connectionTraverser = SysMLv2Mill.traverser()
    connectionTraverser.add4SysMLParts (ConnectionMapping.getInstance())
    asts.forEach { it.accept(connectionTraverser) }

    if(components.isEmpty() && userTypes.isEmpty() && requirements.isEmpty() && calcDefs.isEmpty()) {
      info("Nothing found, exiting")
    }
    else {
      info("\uD83D\uDD0D Pre-type-checking expressions")
      val tcTraverser = SysMLv2Mill.inheritanceTraverser()
      tcTraverser.add4ExpressionsBasis(object : ExpressionsBasisVisitor2 {
        override fun visit(node: ASTExpression) {
          TypeCheck3.typeOf(node)
        }
      })
      artifacts.forEach { it.accept(tcTraverser) }
      info("✅ Pre TypeCheck successfull")

      val sessionGenerator = SessionGenerator(target.resolve("theories"))

      handover(
        bundles,
        components,
        userTypes,
        sysmlTool.inheritanceTraverser,
        calcDefs,
        target,
        comment,
        hwlProvider,
        sessionGenerator,
        channels
      )

      val focusReqs = requirements.map { it ->
        val focusRequirement: ASTRequirement

        if (it.name == "req_SecurityOfGate") {
          val subject = "SecurityGate_LLR"
          val assumptions = listOf(
            "{channel_SecurityGate_LLR_input_dataConstr Alice_plus_Eve_request_Camera_accepts,\n" +
                "    channel_SecurityGate_LLR_input_dataConstr Bob_plus_Eve_request_Camera_accepts} \\\\<inter> eValues\\\\<cdot>input = {}"
          )
          val guarantee = "(StateConstr state__Bob_Alice_Eve) \\\\<notin> sreachableStates (behavior.eaut ())\\\\<cdot>input"
          val proofStartHint = listOf(
            "apply(simp add: sreachableStates_def autInitConfig.rep_eq autTransition.rep_eq behavior.eaut.rep_eq)",
            "apply(simp add: initialConfigs_def eventGen.config_def outconv_def image_comp behavior.ndaInitConfigC_def eventGen.ndaInitConfigC_def)",
            "apply(simp add: reachability_induction assms)"
          )
          focusRequirement = ASTRequirementBuilder()
            .setName(it.name)
            .setSubject(subject)
            .setAssumptionsList(assumptions)
            .setGuarantee(guarantee)
            .setProofStartHintList(proofStartHint)
            .uncheckedBuild()
        } else {
          val printer = Requirement2FocusRequirementPrinter(IndentPrinter(),
            expressionPrinter,
            false)
          printer.visit(it)

          focusRequirement = FocusMill.parser()
            .parse_StringRequirement(printer.content).get()
        }
        focusRequirement
      }

      focusReqs.forEach {
        val session = createSession(it)
        val theory = createTheory(it, session)
        buildSymbolTable(it, session, theory)

        sessionGenerator
          .add(theory)
          .addDependency(theory, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(theory, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
          .addDependency(theory, FocusMill.globalScope().resolveSps(it.subject).get().theorySymbol)

        val subject = FocusMill.globalScope().resolveSps(it.subject).get()
        val containsExecsem = it.guarantee.contains("execsem") ||
          it.assumptionsList.any { assumption -> assumption.contains("execsem") }
        val usesExecutableRequirement =
          it.subjectSymbol is IAutomatonSymbol &&
            (it.subjectSymbol as IAutomatonSymbol).isFinite &&
            it.subjectSymbol.name != "SecurityGate_LLR"

        if (containsExecsem || usesExecutableRequirement) {
          FocusMill.globalScope().resolveTheory("code_${it.subject}.code_${it.subject}")
            .ifPresent { sessionGenerator.addDependency(theory, it) }
          sessionGenerator.addDependency(theory, subject.input.codeTheorySymbol)
          sessionGenerator.addDependency(theory, subject.output.codeTheorySymbol)
        }

        FocusMill.globalScope().resolveBundle(it.subject + ".Input")
          .ifPresent { sessionGenerator.addDependency(theory, it.theorySymbol) }
        FocusMill.globalScope().resolveBundle(it.subject + ".Output")
          .ifPresent { sessionGenerator.addDependency(theory, it.theorySymbol) }

        val template = if (
          it.subjectSymbol is IAutomatonSymbol
          && (it.subjectSymbol as IAutomatonSymbol).isFinite
          && it.subjectSymbol.name != "SecurityGate_LLR"
        ) {
          REQUIREMENT_EXECUTABLE_TEMPLATE
        } else {
          REQUIREMENT_TEMPLATE
        }

        if (!theory.isSubstituted) {
          FreemarkerInterface.instance.generate(
            template,
            target.resolve("theories").resolve(
              session.path.resolve(theory.filename + ".thy")).toAbsolutePath(),
            comment,
            theory,
            it
          )
        }
      }
      sessionGenerator.generate()
    }
  }

  @JvmStatic
  fun handover(
    bundleModels: List<String>,
    components: List<MildComponentSymbol>,
    userTypes: List<TypeSymbol>,
    traverser: SysMLv2Traverser,
    calcDefs: List<String>,
    target: Path,
    comment: Boolean,
    hwlProvider: AHwlProvider,
    sessionGenerator: SessionGenerator,
    channelModels: List<String>
  ) {
    val focusTool = FocusTool()
    focusTool.init()
    FocusMill.setHwlProvider(hwlProvider)

    FreemarkerInterface.instance.glex
      .setGlobalValue("typePrinter", TypePrinter())

    val targetSymbols = target.resolve("focusSymbols")
    focusTool.setup(targetSymbols)

    val targetTheories = target.resolve("theories")
    val globalScope = FocusMill.globalScope()

    val chanTypes = components
      .flatMap { ChannelFunctions.createChanType(it, TypePrinter()) }
      .sortedBy { it.name }

    ifAnyThenInfo(chanTypes, "", "Found # distinct channel types")

    DataInc.generateUserDataInc(
      targetTheories,
      userTypes,
      chanTypes,
      calcDefs,
      TypePrinter(),
      sessionGenerator,
      comment
    )

    channelModels.forEach { model ->
      val channel = FocusMill.parser().parse_StringChannel(model).get()
      focusTool.createSymbolTable(channel)
      focusTool.completeSymbolTable(channel)
    }

    val bundles = mutableListOf<ASTBundle>()
    bundleModels.forEach {
      var b = Bundles.transformBundles(
          it,
          targetTheories,
          sessionGenerator,
          comment
      )
      bundles += b
      info("Parsed and generated theories for ${b.name}")
    }

    components.filter { it.isAtomic }.forEach {
      if (it.isEventBased) {
        EventAutomaton.transformEventAutomaton(
            targetTheories,
            it,
            globalScope.resolveBundle(it.refinementStart.get().fullName + ".Input").get(),
            globalScope.resolveBundle(it.refinementStart.get().fullName + ".Output").get(),
            getEventExpressionPrinter(traverser),
            TypePrinter(),
            sessionGenerator,
            comment
        )
      }
      else if(it.isTsynStateBased) {
        TsynAutomaton.transformTSynAutomaton(
          targetTheories,
          it,
          globalScope.resolveBundle(it.refinementStart.get().fullName + ".Input").get(),
          globalScope.resolveBundle(it.refinementStart.get().fullName + ".Output").get(),
          getTsynAutExpressionPrinter(traverser),
          TypePrinter(),
          sessionGenerator,
          comment
        )
      }
      else {
        val expressionPrinter = if (it.isTsynHistoryBased) {
          getTsynSpecExpressionPrinter(traverser)
        } else {
          getEventExpressionPrinter(traverser)
        }
        Sps.transformSpec(
          targetTheories,
          it,
          globalScope.resolveBundle(it.refinementStart.get().fullName + ".Input").get(),
          globalScope.resolveBundle(it.refinementStart.get().fullName + ".Output").get(),
          expressionPrinter,
          TypePrinter(),
          comment,
          sessionGenerator
        )
      }
    }

    val eventExpressionPrinter = getEventExpressionPrinter(traverser)
    components.filter { it.isDecomposed }.forEach { component ->
      component.subcomponents.map { part ->
        part as MildInstanceSymbol

        Transformer.generateInstance(
          targetTheories,
          part,
          component,
          eventExpressionPrinter,
          TypePrinter(),
          comment,
          sessionGenerator
        )
      }

      Transformer.transformComp(
        targetTheories,
        component,
        globalScope.resolveBundle(component.refinementStart.get().fullName + ".Input").get(),
        globalScope.resolveBundle(component.refinementStart.get().fullName + ".Output").get(),
        TypePrinter(),
        comment,
        sessionGenerator
      )
    }

    components.forEach { component ->
      if (component.refinementStart.isPresent && component.refinementStart.get() != component) {
        component.refinementsList.forEach {
          val (ref, th) = Refinement.generateRefinement(
            it.typeInfo,
            component,
            sessionGenerator
          )


          if(!th.isSubstituted()) {
            val template = if(ref.isAutomaticHlrNarrowing) {
              AUTOMATIC_HLR_NARROWING
            } else if(ref.isCompositeHlrNarrowing) {
              COMPOSITE_HLR_NARROWING
            } else if(ref.isHlrDecomposition) {
              HLR_DECOMPOSITION
            } else if(ref.hasMatchingEventAutomata()) {
              EVENTAUT_REF
            } else if(ref.hasMatchingTimesliceAutomata()) {
              TSYNAUT_REF
            } else if(ref.isLlrRefinementEvent) {
              EVENT_LLR2HLR
            } else {
              GENERAL_REF
            }

            FreemarkerInterface.instance.generate(
              template,
              targetTheories.resolve(th.session.path.resolve(th.filename + ".thy"))
                .toAbsolutePath(),
              comment,
              th,
              ref
            )

            sessionGenerator
              .addDependency(th, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
              .addDependency(th, FocusMill.globalScope().resolveTheory("user.Datatypes").get())

            th.session.addImportSession("Smart_Isabelle")
            if (ref.isCompositeHlrNarrowing) {
              th.session.addImportSession("generator")
            }

            sessionGenerator
              .addDependency(th, ref.roughNameSymbol.theorySymbol)
              .addDependency(th, ref.refinedNameSymbol.theorySymbol)

            if(ref.transitiveRefinements.isNotEmpty()) {
              sessionGenerator.addDependenciesOnSymbol(th,
                ref.transitiveRefinements.map { it.theorizedBy })
            }

            if(ref.subComponentRefinements.isNotEmpty()) {
              sessionGenerator.addDependenciesOnSymbol(th,
                ref.subComponentRefinements.map { it.theorizedBy })
            }
          }
        }
      }
    }

    globalScope.subScopes
      .forEach {
        focusTool.storeSymbols(
          (it as IFocusArtifactScope),
          targetSymbols,
          "${it.name}.sym"
        )
      }
  }

  @JvmStatic
  fun getEventExpressionPrinter(traverser: SysMLv2Traverser): IExpressionPrinter {
    val printer = ResettableIndentPrinter()
    val settings = IsabellePrinterSettings()
    return buildExpressionPrinter(
      traverser,
      printer,
      CommonExpressions2Isabelle(printer, settings),
      MCCommonLiterals2Isabelle(printer),
      ExpressionsBasis2Isabelle(printer, settings),
      SysMLExpressions2Isabelle(printer, settings),
    )
  }

  @JvmStatic
  fun getTsynSpecExpressionPrinter(traverser: SysMLv2Traverser): IExpressionPrinter {
    val printer = ResettableIndentPrinter()
    val settings = IsabellePrinterSettings()
    return buildExpressionPrinter(
      traverser,
      printer,
      TsynCommonExpressions2Isabelle(printer, settings),
      MCCommonLiterals2Isabelle(printer),
      ExpressionsBasis2Isabelle(printer, settings),
      SysMLExpressions2Isabelle(printer, settings),
    )
  }

  @JvmStatic
  fun getTsynAutExpressionPrinter(traverser: SysMLv2Traverser): IExpressionPrinter {
    val printer = ResettableIndentPrinter()
    val settings = IsabellePrinterSettings()
    return buildExpressionPrinter(
      traverser,
      printer,
      TsynAutomatonCommonExpressions2Isabelle(printer, settings),
      TsynAutomatonMCCommonLiterals2Isabelle(printer),
      TsynAutomatonExpressionsBasis2Isabelle(printer, settings),
      TsynAutomatonSysMLExpressions2Isabelle(printer, settings),
    )
  }

  private fun buildExpressionPrinter(
    traverser: SysMLv2Traverser,
    printer: ResettableIndentPrinter,
    commonExpressions: CommonExpressions2Isabelle,
    mcCommonLiterals: MCCommonLiteralsVisitor2,
    expressionsBasis: ExpressionsBasis2Isabelle,
    sysmlExpressions: SysMLExpressions2Isabelle,
  ): IExpressionPrinter {
    val printerTraverser = traverser

    commonExpressions.traverser = printerTraverser
    printerTraverser.setCommonExpressionsHandler(commonExpressions)
    printerTraverser.add4CommonExpressions(commonExpressions)
    printerTraverser.add4MCCommonLiterals(mcCommonLiterals)

    expressionsBasis.traverser = printerTraverser
    printerTraverser.add4ExpressionsBasis(expressionsBasis)
    printerTraverser.setExpressionsBasisHandler(expressionsBasis)

    val sysmlParts = SysMLParts2Isabelle(printer)
    sysmlParts.traverser = printerTraverser
    printerTraverser.add4SysMLParts(sysmlParts)

    val assignmentExpressions = AssignmentExpressions2Isabelle(printer)
    assignmentExpressions.traverser = printerTraverser
    printerTraverser.add4AssignmentExpressions(assignmentExpressions)
    printerTraverser.setAssignmentExpressionsHandler(assignmentExpressions)

    val oclExpressions = OCLExpressions2Isabelle(printer)
    oclExpressions.traverser = printerTraverser
    printerTraverser.add4OCLExpressions(oclExpressions)
    printerTraverser.setOCLExpressionsHandler(oclExpressions)

    val setExpressions = SetExpressions2Isabelle(printer)
    setExpressions.traverser = printerTraverser
    printerTraverser.add4SetExpressions(setExpressions)
    printerTraverser.setSetExpressionsHandler(setExpressions)

    sysmlExpressions.traverser = printerTraverser
    printerTraverser.add4SysMLExpressions(sysmlExpressions)
    printerTraverser.setSysMLExpressionsHandler(sysmlExpressions)

    val streamExpresions = StreamExpressions2Isabelle(printer)
    streamExpresions.traverser = printerTraverser
    printerTraverser.add4StreamExpressions(streamExpresions)
    printerTraverser.setStreamExpressionsHandler(streamExpresions)

    val expressionPrinter = object : IExpressionPrinter {
      override val printer: ResettableIndentPrinter
        get() = printer
      override val traverser: SysMLv2Traverser
        get() = printerTraverser
    }

    return expressionPrinter
  }

}
