package montibelle.transformer.generic.sessions

import de.se_rwth.commons.logging.Log
import montibelle.focus.FocusMill
import montibelle.focus._ast.*
import montibelle.focus._symboltable.TheorySymbol
import montibelle.transformer.generic.Constants
import montibelle.transformer.generic.meta.bundle.IBundle
import montibelle.transformer.generic.meta.bundle.ICodeBundle
import montibelle.transformer.util.FreemarkerInterface
import java.nio.file.Path

class SessionGenerator(
  private val target: Path
) {

  companion object {

    fun addDependency(target: ASTSession, source: TheorySymbol) {
      val sourceSession = source.session

      FocusMill.getHwlProvider()
          .getEpilogueSessionsFor(sourceSession.name, source.filename)
          .forEach {
            if(it !in target.importSessions)
              target.addImportSession(it)
          }

      if(target.name != sourceSession.name
          && !target.importSessions.contains(sourceSession.name))
      {
        target.addImportSession(sourceSession.name)
      }

    }

  }

  private var rootFiles: MutableMap<Path, MutableList<ASTSession>> = HashMap()

  private var rootsFiles: MutableMap<Path, MutableSet<Path>> = HashMap()

  private fun _parentDirOf(theory: ASTTheory): Path {
    return target.resolve(theory.session.path)
  }

  fun get(theory: ASTTheory): ASTSession {
    val existingRoot = rootFiles[_parentDirOf(theory)]
    val existingSession = existingRoot?.firstOrNull { session -> session.name == theory.session.name }
    val session = existingSession ?: theory.session

    val existingRootInOtherDirectory = rootFiles.filter {
      it.value.any { it.name == theory.session.name } && it.key != _parentDirOf(theory)
    }
    if(existingRootInOtherDirectory.any()) {
      Log.warn(
        "Session named ${theory.session.name} already exists in ${existingRootInOtherDirectory.entries.first().key}"
      )
    }

    if(existingRoot == null) {
      rootFiles[_parentDirOf(theory)] = mutableListOf(session)
    }
    else if(existingSession == null) {
      existingRoot.add(session)
    }

    return session
  }

  private fun putInRoots(roots: Path, paths: Collection<Path>) {
    val existingPaths = rootsFiles[roots]
    if(existingPaths != null) {
      existingPaths.addAll(paths)
    }
    else {
      rootsFiles[roots] = paths.toMutableSet()
    }
  }

  fun addAll(theories: List<ASTTheory>): SessionGenerator {
    theories.forEach { this.add(it) }
    return this
  }

  fun add(theory: ASTTheory): SessionGenerator {
    val session = get(theory)

    if(session.theories == null || session.theories!!.size == 0) {
      session.addTheory(Theories(TheoryEntry(theory.filename)))
    }
    else {
      val existing = ArrayList(session.theories[0].theoryEntries)
      if (TheoryEntry(theory.filename) !in existing) {
        existing.add(TheoryEntry(theory.filename))
        session.theories!![0].theoryEntries = existing
      }
    }

    theory.prologueSessions.forEach { if(it !in session.importSessions) session.addImportSession(it) }

    return this
  }

  fun addDependency(target: ASTTheory, source: ASTTheory): SessionGenerator {
    val targetSession = get(target)
    val sourceSession = get(source)

    source.epilogueSessions.forEach {
      if (it !in targetSession.importSessions) targetSession.addImportSession(it)
    }

    var substitute = FocusMill.getHwlProvider().substituteFor(source.session.name, source.filename)
    if(substitute != null) {
      var substituteSession = substitute.sessionName

      if (targetSession.name != substituteSession &&
          !targetSession.importSessions.contains(substituteSession))
      {
        targetSession.addImportSession(substituteSession)
      }
    }
    else {
      if (targetSession.name != sourceSession.name &&
          !targetSession.importSessions.contains(sourceSession.name))
      {
        targetSession.addImportSession(sourceSession.name)
        putInRoots(_parentDirOf(target), mutableListOf(_parentDirOf(source)))
      }
    }

    return this
  }



  fun addDependencies(target: ASTTheory, sources: List<ASTTheory>): SessionGenerator {
    sources.forEach { source -> addDependency(target, source) }
    return this
  }

  fun addAllDependencies(targets: List<ASTTheory>, source: ASTTheory): SessionGenerator {
    targets.forEach { target -> addDependency(target, source) }
    return this
  }

  fun generate() {
    for (rootFile in rootFiles) {
      val pathOf = { entry: Map.Entry<Path, MutableList<ASTSession>> -> entry.key }
      val sessionsOf = { entry: Map.Entry<Path, MutableList<ASTSession>> -> entry.value }

      try {
        FreemarkerInterface.instance.generate(
          Constants.ROOT_TEMPLATE,
          pathOf(rootFile).resolve("ROOT").toAbsolutePath(), sessionsOf(rootFile)
        )
      }
      catch (ex: Exception) {
        Log.error("Exception occurred while generating ROOT-files: " + ex.message, ex)
      }
    }

    for (folder in target.toFile().walk().filter { it.isDirectory }) {
      val foldersWithSessions = folder.walk().maxDepth(1)
        .filter { it.isDirectory && it != folder && it.walk().any { f -> (f.name == "ROOT") } }
        .map { it.toPath() }
        .toMutableSet()

      if (!folder.walk().maxDepth(1).any { f -> f.name == "ROOT" } || rootFiles[folder.toPath()] != null) {
        putInRoots(folder.toPath(), foldersWithSessions)
      }
    }

    for (rootsFile in rootsFiles) {
      if(rootsFile.value.any()) {
        try {
          FreemarkerInterface.instance.generate(Constants.ROOTS_TEMPLATE,
            rootsFile.key.resolve("ROOTS").toAbsolutePath(),
            rootsFile.value.map { path -> rootsFile.key.relativize(path).toString().replace("\\", "/") }.sorted()
          )
        }
        catch (ex: Exception) {
          Log.error("Exception occurred while generating ROOTS-files: " + ex.message, ex)
        }
      }
    }
  }

  private fun _parentDirOf(theory: TheorySymbol): Path {
    return target.resolve(theory.enclosingScope.resolveSession(theory.sessionName).get().path)
  }

  fun addDependency(target: ASTTheory, source: TheorySymbol): SessionGenerator {
    val targetSession = get(target)
    val sourceSession = source.enclosingScope.resolveSession(source.sessionName).get()


    if(targetSession.name != sourceSession.name
      && !targetSession.importSessions.contains(sourceSession.name))
    {
      targetSession.addImportSession(sourceSession.name)
      putInRoots(_parentDirOf(target), mutableListOf(_parentDirOf(source)))
    }

    return this
  }

  fun addDependenciesOnSymbol(target: ASTTheory, sources: List<TheorySymbol>): SessionGenerator {
    sources.forEach { source -> addDependency(target, source) }
    return this
  }

  fun addAllDependenciesOnSymbol(targets: List<ASTTheory>, source: TheorySymbol): SessionGenerator {
    targets.forEach { target -> addDependency(target, source) }
    return this
  }
}
