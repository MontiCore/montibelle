import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import montibelle.focus._ast.ASTSession
import montibelle.focus._ast.ASTSessionBuilder
import montibelle.transformer.generic.Constants
import montibelle.transformer.generic.sessions.DocumentFiles
import montibelle.transformer.generic.sessions.ExportFiles
import montibelle.transformer.generic.sessions.Options
import montibelle.transformer.generic.sessions.Theories
import montibelle.transformer.generic.sessions.TheoryEntry
import org.assertj.core.api.Assertions
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import montibelle.transformer.util.FreemarkerInterface
import java.io.IOException
import java.io.StringWriter
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.util.*

class RootTest {

  companion object {
    private const val SESSION_NAME = "test_session"

    private val OPTION_WITHOUT_VALUE = Options("option1")
    private val OPTION_WITH_VALUE = Options("option2", "value")
    private val OPTIONS = Arrays.asList(OPTION_WITHOUT_VALUE, OPTION_WITH_VALUE)
    private val EXPECTED_FILE_DIR = Paths.get("src/test/resources/montibelle/transformer/generic/sessions").toAbsolutePath()
    private val EXPECTED_MINIMAL_SESSION_FILE = EXPECTED_FILE_DIR.resolve("minimal_session.txt")
    private val EXPECTED_SESSION_WITH_GROUPS_FILE = EXPECTED_FILE_DIR.resolve("group_session.txt")
    private val EXPECTED_SESSION_WITH_DIR_FILE = EXPECTED_FILE_DIR.resolve("dir_session.txt")
    private val EXPECTED_SESSION_WITH_PARENT_FILE = EXPECTED_FILE_DIR.resolve("parent_session.txt")
    private val EXPECTED_SESSION_WITH_DESCRIPTION_FILE = EXPECTED_FILE_DIR.resolve("description_session.txt")
    private val EXPECTED_SESSION_WITH_OPTIONS_FILE = EXPECTED_FILE_DIR.resolve("options_session.txt")
    private val EXPECTED_SESSION_WITH_IMPORT_SESSIONS_FILE = EXPECTED_FILE_DIR.resolve("import_sessions_session.txt")
    private val EXPECTED_SESSION_WITH_THEORIES_FILE = EXPECTED_FILE_DIR.resolve("theories_session.txt")
    private val EXPECTED_SESSION_WITH_DOCUMENT_FILES_FILE = EXPECTED_FILE_DIR.resolve("document_files_session.txt")
    private val EXPECTED_SESSION_WITH_EXPORT_FILES_FILE = EXPECTED_FILE_DIR.resolve("export_files_session.txt")

    private lateinit var session: ASTSession
    private var expected: String? = null

    @Throws(IOException::class)
    private fun read(file: Path): String {
      return String(Files.readAllBytes(file))
    }
  }

  @BeforeEach
  fun setUp() {
    session = ASTSessionBuilder().setName(SESSION_NAME).build()
    session.parent = null
    session.groups = mutableListOf()
    LogStub.init()
    Log.getFindings().clear()
  }

  @Test
  @Throws(IOException::class)
  fun testMinimalSession() {
    expected = read(EXPECTED_MINIMAL_SESSION_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithGroups() {
    session.groups = Arrays.asList("group1", "group2")
    expected = read(EXPECTED_SESSION_WITH_GROUPS_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithDir() {
    session.dir = "./some/dir"
    expected = read(EXPECTED_SESSION_WITH_DIR_FILE)
  }

  @Test @Throws(IOException::class) fun testSessionWithParent() {
    session.parent = "parent"
    expected = read(EXPECTED_SESSION_WITH_PARENT_FILE)
  }

  @Test @Throws(IOException::class) fun testSessionWithDescription() {
    session.description = "some description"
    expected = read(EXPECTED_SESSION_WITH_DESCRIPTION_FILE)
  }

  @Test @Throws(IOException::class) fun testSessionWithOptions() {
    session.options = OPTIONS
    expected = read(EXPECTED_SESSION_WITH_OPTIONS_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithImportSessions() {
    session.importSessions = Arrays.asList("import1", "import2")
    expected = read(EXPECTED_SESSION_WITH_IMPORT_SESSIONS_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithTheories() {
    val theories = ArrayList(Arrays.asList(
        Theories(OPTIONS, Arrays.asList(TheoryEntry("Theory 1"))),
        Theories(
            Arrays.asList(TheoryEntry("Theory 2"), TheoryEntry("Theory 3", true))
        )
    ))
    session.theories = theories
    expected = read(EXPECTED_SESSION_WITH_THEORIES_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithDocumentFiles() {
    session.documentFiles = Arrays.asList(
        DocumentFiles(
            "./document/dir",
            Arrays.asList("document1", "document2")
        ),
        DocumentFiles("document3")
    )
    expected = read(EXPECTED_SESSION_WITH_DOCUMENT_FILES_FILE)
  }

  @Test
  @Throws(IOException::class)
  fun testSessionWithIOExportFiles() {
    session.exportFiles = Arrays.asList(
        ExportFiles("./export/dir", 2, listOf("export1", "export2")),
        ExportFiles(listOf("export3"))
    )
    expected = read(EXPECTED_SESSION_WITH_EXPORT_FILES_FILE)
  }

  @AfterEach
  @Throws(IOException::class)
  fun fileCompare() {
    val writer = StringWriter()

    FreemarkerInterface.instance.generate(Constants.ROOT_TEMPLATE
        , writer
        , listOf(session))

    val outcome = writer.toString()

    Assertions.assertThat(outcome).isEqualToIgnoringWhitespace(expected)
  }
}
