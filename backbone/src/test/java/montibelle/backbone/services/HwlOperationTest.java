package montibelle.backbone.services;

import montibelle.backbone.hwl.OperationInput;
import montibelle.backbone.hwl.RetrievalInput;
import montibelle.backbone.workspace.Parameters;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.util.ReflectionTestUtils;

import java.io.File;
import java.net.URI;
import java.nio.file.Path;
import java.nio.file.Paths;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertArrayEquals;

@SpringBootTest
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class HwlOperationTest {

  @Autowired
  private WorkspaceService workspaceService;

  @Autowired
  private HwlService hwlService;

  @Autowired
  private WorkspaceService workspaceManager;

  final static String BASE = "target/test-classes";

  final static URI SOURCE = new File(BASE + "/source").toURI();
  final static URI TARGET = new File(BASE + "/target").toURI();
  final static URI HWL = new File(BASE + "/hwls/HWLS.yaml").toURI();

  final static File WORKSPACE_YAML = new File(BASE + "/backbone_workspaces.yaml");

  private String WORKSPACE_ID;

  @BeforeAll
  public void initWorkspace() throws Exception {
    ReflectionTestUtils.setField(workspaceManager, "workspacesPath", WORKSPACE_YAML.toString());
    WORKSPACE_ID = workspaceService.register(new Parameters(SOURCE.toString(), TARGET.toString(), HWL.toString()));
  }

  @Test
  public void testAdd() throws Exception {
    OperationInput input = new OperationInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Broken",
        true,
        "demo",
        "Visual"
    );
    hwlService.add(input);

    RetrievalInput viewInput = new RetrievalInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Broken"
    );

    assertThat(hwlService.getHwlsForTheory(viewInput)).isEqualTo(new String[] { "demo.Visual" });
  }

  @Test
  public void testRemove() throws Exception {
    OperationInput input = new OperationInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Important",
        false,
        "fancy",
        "Custom");

    hwlService.add(input);
    hwlService.remove(input);

    RetrievalInput viewInput = new RetrievalInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Important");

    assertThat(hwlService.getHwlsForTheory(viewInput)).isEqualTo(new String[] {});
  }

  @Test
  public void testGetHwlsForTheory() throws Exception {
    OperationInput input = new OperationInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Test",
        false,
        "fancy",
        "Custom");
    hwlService.add(input);

    OperationInput input2 = new OperationInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Test",
        false,
        "mundane",
        "Custom");
    hwlService.add(input2);

    RetrievalInput viewInput = new RetrievalInput(
        WORKSPACE_ID,
        "generated",
        "def_code_Test");

    assertThat(hwlService.getHwlsForTheory(viewInput)).isEqualTo(new String[] { "fancy.Custom", "mundane.Custom" });
  }

}
