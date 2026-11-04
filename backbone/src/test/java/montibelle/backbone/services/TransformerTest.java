package montibelle.backbone.services;

import montibelle.backbone.util.FileUtil;
import montibelle.backbone.workspace.Parameters;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;
import org.springframework.test.util.ReflectionTestUtils;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.assertj.core.api.AssertionsForInterfaceTypes.assertThat;
import static org.junit.jupiter.api.Assertions.assertTrue;

@SpringBootTest
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class TransformerTest {

  private static final String BASE = "src/test/resources/montibelle/backbone/services/transformer";
  private static final String WORKSPACE = BASE + "/backbone_workspaces.yaml";
  public static final String VERSION = "2.2.0-20220912.124202-1";

  @Autowired
  private TransformerService transformerService;

  @Autowired
  private WorkspaceService workspaceService;

  @BeforeAll
  public void init() {
    ReflectionTestUtils.setField(workspaceService, "workspacesPath", WORKSPACE);
  }

  @Test
  @Disabled
  public void testDownload() throws IOException {
    transformerService.downloadTransformerJar(Path.of("target/test-classes"), VERSION, true);
  }

  @Test
  @Disabled
  public void testSuccess() throws Exception {
    Path source = Path.of(BASE + "/models");
    Path target = Path.of(BASE + "/theories");

    Parameters workdirDefinition = new Parameters(source.toUri().toString(), target.toUri().toString(), null);
    String workspaceId = workspaceService.register(workdirDefinition);

    File transformLogFile = new File(transformerService.transform(workspaceId, VERSION, Path.of("target/test-classes")));
    assertTrue(transformLogFile.exists());
  }

  @Test
  @Disabled
  public void testFailure() throws Exception {
    Path target = Path.of(BASE + "/theories");

    Parameters workdirDefinition = new Parameters(null, target.toUri().toString(), null);
    String workspaceId = workspaceService.register(workdirDefinition);

    Assertions.assertThrows(Exception.class, () -> transformerService.transform(workspaceId, VERSION));
    assertThat(target).doesNotExist();
  }

  @AfterEach
  public void cleanUp() throws IOException {
    Path workspace_yaml = Path.of(WORKSPACE);
    Files.deleteIfExists(workspace_yaml);
    FileUtil.deleteDirectory(Path.of(BASE + "/theories"));
  }

}
