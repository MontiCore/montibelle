package montibelle.backbone.services;

import montibelle.backbone.services.WorkspaceService;
import montibelle.backbone.workspace.Parameters;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestInstance;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.context.SpringBootTest;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;

import static org.junit.jupiter.api.Assertions.*;

@SpringBootTest
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class RegisterWorkspaceTest {

  @Autowired
  private WorkspaceService workspaceService;

  private static String baseUri = new File("src/test/resources/montibelle/backbone/transformer").toURI()
      .toString();

  private static String SOURCE = baseUri + "models";
  private static String TARGET = baseUri + "theories";
  private static String HWL = baseUri + "hwl";

  private String workspaceId;

  @BeforeEach
  public void register() throws IOException, URISyntaxException {
    Parameters workdirDefinition = new Parameters(SOURCE, TARGET, HWL);
    workspaceId = workspaceService.register(workdirDefinition);
    assertNotNull(workspaceId);
  }

  @Test
  public void testRegisterWorkspace() throws Exception {
    Parameters workdirDefinitionActual = workspaceService.retrieve(workspaceId);
    assertEquals(SOURCE, workdirDefinitionActual.getSourceUri());
    assertEquals(TARGET, workdirDefinitionActual.getTargetUri());
    assertTrue(workdirDefinitionActual.getHwlUri().isPresent());
    assertEquals(HWL, workdirDefinitionActual.getHwlUri().get());
  }

  @AfterEach
  public void deregister() throws Exception {
    workspaceService.remove(workspaceId);
  }

}
