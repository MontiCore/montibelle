package montibelle.transformer.generic.theories;

import de.se_rwth.commons.logging.Log;
import montibelle.focus._ast.ASTTheory;
import montibelle.transformer.util.FreemarkerInterface;
import java.nio.file.Path;

public final class TheoryGenerator{

  private TheoryGenerator() {
  }

  public static void print(
      Object element,
      ASTTheory theory,
      Path target,
      boolean comment,
      String template
  ) {
    try {
      FreemarkerInterface.instance.generate(
          template,
          target.resolve(
              theory.getSession().getPath().resolve(theory.getFilename() + ".thy")
          ).toAbsolutePath(),
          comment,
          theory,
          element
      );
    } catch (Exception ex) {
      Log.error(
          "Exception occurred while generating the theory " + target + ": " + ex.getMessage(),
          ex
      );
    }
  }
}

