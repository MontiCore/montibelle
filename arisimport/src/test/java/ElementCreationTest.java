import com.nomagic.magicdraw.core.Application;
import com.nomagic.magicdraw.core.Project;
import com.nomagic.magicdraw.export.image.ImageExporter;
import com.nomagic.magicdraw.openapi.uml.SessionManager;
import com.nomagic.magicdraw.tests.MagicDrawTestRunner;
import com.nomagic.magicdraw.uml.symbols.layout.composite.CompositeStructureDiagramLayouter;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.Diagram;
import de.se_rwth.commons.logging.Log;
import epc.EPCMill;
import epc.EpcImporter;
import org.junit.*;
import org.junit.rules.TestName;
import org.junit.runner.RunWith;

import java.awt.*;
import java.io.File;
import java.io.IOException;

import static bpmn.Importer.getOrCreateProject;
import static org.assertj.core.api.Assertions.assertThat;
import static org.assertj.core.api.Fail.fail;

@RunWith(MagicDrawTestRunner.class)
public class ElementCreationTest {

  Project project;

  @BeforeClass
  public static void init() {
    Log.init();
    EPCMill.init();
  }

  @Before
  public void getProject() {
    project = getOrCreateProject();
  }

  @Rule
  public TestName testName = new TestName();

  @After
  public void closeProject() {
    Application.getInstance().getProjectsManager().closeProject();
    project = null;
  }

  @Test
  public void testImportWeightProcess() {
    var importer = new EpcImporter(new File(
        "src/test/resources/CreateWeightCalculationForecast.txt"));
    var res = importer.doImport();

    assertThat(res).isTrue();
    assertThat(importer.getDiagrams()).hasSize(1);

    exportImage(importer.getDiagrams().get(0));
  }

  @Test
  public void testImportUnterschriftenProzess() {
    var importer = new EpcImporter(new File(
        "src/test/resources/DefiniereUnterzeichnerDerDesignOrganisation.txt"));
    var res = importer.doImport();

    assertThat(res).isTrue();
    assertThat(importer.getDiagrams()).hasSize(1);

    exportImage(importer.getDiagrams().get(0));
  }

  @Test
  public void testCreateEventAcceptAction() throws IOException {
    var project = getOrCreateProject();
    SessionManager.getInstance().createSession(project, "Create a diagram");
    var importer = new EpcImporter(new File(""));

    var diag =
        "\"MyDiagram\" " +
            "Properties " +
            "Properties " +
            "Type                \"MyType\" " +
            "Group               \"MyGroup\" " +
            "Time of generation  Jan 1 1900 00:00:00 AM " +
            "Creator             name@domain.tld " +
            "Last change         Jan 1 1900 00:00:00 AM " +
            "Last user           name@domain.tld " +
            "Objects " +
            "Graphic ";
    var astDiagram = EPCMill.parser().parse_StringDiagram(diag).get();

    var diagram = importer.createDiagram(project, astDiagram);

    var eventObj =
        "\"MyObject\" " +
            "Properties " +
            "Type               \"Event\" " +
            "Group              \"MyGroup\" " +
            "Time of generation Jan 1 1900 00:00:00 AM " +
            "Creator            name@domain.tld " +
            "Last change        Jan 1 1900 00:00:00 AM " +
            "Last user          name@domain.tld " +
            "Relationships " +
            "Relationship type  Object name  Object type";
    var astObject = EPCMill.parser().parse_StringObject(eventObj).get();

    var shape = importer.createEventAcceptAction(project, diagram, astObject);
    shape.setFillColor(Color.GREEN);

    SessionManager.getInstance().closeSession(project);
    exportImage(diagram);
  }

  protected void exportImage(Diagram diagram) {
    String methodName = Thread.currentThread()
        .getStackTrace()[2]
        .getMethodName();
    var dpe = project.getDiagram(diagram);
    dpe.open();
    dpe.layout(false, new CompositeStructureDiagramLayouter());
    var file = new File("src/test/resources/images/" + methodName + ".png");
    try {
      ImageExporter.export(dpe, ImageExporter.PNG, file);
    }
    catch (IOException e) {
      fail(String.format("Could not take image for %", methodName));
    }
  }

}
