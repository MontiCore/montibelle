package montibelle.backbone.services;

import de.se_rwth.commons.logging.Log;
import montibelle.backbone.ProofState;
import montibelle.backbone.Proof;
import montibelle.backbone.proof.ProveDefinition;
import montibelle.backbone.util.FileUtil;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Paths;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;

public class ProofServiceTest {

  private static final String simpleProofDir = "src/test/resources/montibelle/backbone/autosledgi/simpleproof";

  private static final String simpleProofDirTmp = "src/test/resources/montibelle/backbone/autosledgi/simpleproof_tmp";

  @BeforeAll
  public static void prepareSimpleProof() throws IOException {
    FileUtil.deleteDirectory(Paths.get(simpleProofDirTmp));
    FileUtil.copyDirectory(simpleProofDir, simpleProofDirTmp);
  }

  @Test
  public void testVerifyWithUnsolvedLemma() throws IOException, InterruptedException {
    var def = new ProveDefinition("id", simpleProofDirTmp, "HOLCF", new String[]{}, 5, false);
    var testee = new Proof(def, null);

    Log.info("Start", ProofServiceTest.this.getClass().getName());
    testee.verify();

    do {
      Log.info(testee.getProofState().toString(), ProofServiceTest.this.getClass().getName());
      TimeUnit.SECONDS.sleep(1);
    }
    while(testee.getProofState() == ProofState.RUNNING);

    ProofState res = testee.getProofState();

    assert res == ProofState.DISPROVEN;
  }

  @AfterAll
  public static void clearSimpleProof() throws IOException {
    FileUtil.deleteDirectory(Paths.get(simpleProofDirTmp));
  }

}
