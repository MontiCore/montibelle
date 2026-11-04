package montibelle.backbone;

import de.se_rwth.commons.logging.Log;
import montibelle.backbone.autosledgi.AutosledgiWrapper;
import montibelle.backbone.autosledgi.IAutosledgiListener;
import montibelle.backbone.util.FileUtil;
import montibelle.backbone.util.IProcessListener;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;

public class AutosledgiWrapperTest {

  private static final String simpleProofDir = "src/test/resources/montibelle/backbone/autosledgi/simpleproof";

  private static final String simpleProofDirTmp = "src/test/resources/montibelle/backbone/autosledgi/simpleproof_tmp";

  @BeforeAll
  public static void prepareSimpleProof() throws IOException {
    FileUtil.deleteDirectory(Paths.get(simpleProofDirTmp));
    FileUtil.copyDirectory(simpleProofDir, simpleProofDirTmp);
  }

  @Test
  public void SimpleProof() throws IOException, InterruptedException {
    AutosledgiWrapper wrapper = new AutosledgiWrapper(Path.of(simpleProofDirTmp), "HOLCF", new ArrayList<>());

    final int[] async_solved = { 0 };
    final int[] async_unsolved = { 0 };

    wrapper.addListener(new IAutosledgiListener() {
      @Override
      public void onStarted() {
        Log.info("Started!", AutosledgiWrapperTest.this.getClass().getName());
      }

      @Override
      public void onStopped(int exitCode) {
        Log.info("Stopped!", AutosledgiWrapperTest.this.getClass().getName());
      }


      @Override
      public void onProgress(String progress) {
        Log.info(progress, AutosledgiWrapperTest.this.getClass().getName());
      }

      @Override
      public void onProofResultChanged(int solved, int failed) {
        async_unsolved[0] = failed;
        async_solved[0] = solved;
      }

    });

    wrapper.start();
    int code = wrapper.waitForExit();

    assert async_solved[0] == 1;
    assert async_unsolved[0] == 1;

    assert wrapper.getSolvedProofs() == 1;
    assert wrapper.getUnsolvedProofs() == 1;


  }

  @AfterAll
  public static void clearSimpleProof() throws IOException {
    FileUtil.deleteDirectory(Paths.get(simpleProofDirTmp));
  }

}
