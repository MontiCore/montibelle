package montibelle.transformer.util;

import de.monticore.generating.GeneratorEngine;
import de.monticore.generating.GeneratorSetup;
import de.monticore.generating.templateengine.GlobalExtensionManagement;
import de.monticore.generating.templateengine.HookPoint;
import de.monticore.generating.templateengine.reporting.Reporting;
import freemarker.template.Configuration;
import java.io.Writer;
import java.nio.file.Path;

public final class FreemarkerInterface {

  public static final FreemarkerInterface instance = new FreemarkerInterface();
  private final GeneratorEngine generatorEngine;
  private final GlobalExtensionManagement glex;

  private FreemarkerInterface() {
    CustomGeneratorSetup generatorSetup = new CustomGeneratorSetup();

    GlobalExtensionManagement glex = new GlobalExtensionManagement() {

      @Override
      public void bindHookPoint(String hookName, HookPoint hp) {
        Reporting.reportSetHookPoint(hookName, hp);
        hookPoints.put(hookName, hp);
      }
    };

    generatorSetup.setGlex(glex);
    generatorSetup.setTracing(false);

    this.generatorEngine = new GeneratorEngine(generatorSetup);
    this.glex = glex;
  }

  public GeneratorEngine getGeneratorEngine() {
    return generatorEngine;
  }

  public GlobalExtensionManagement getGlex() {
    return glex;
  }

  public void generate(String templateName, Path outFile, Object... args) {
    generatorEngine.generateNoA(templateName, outFile, args);
  }

  public void generate(String templateName, Writer outWriter, Object... args) {
    generatorEngine.generateNoA(templateName, outWriter, args);
  }
}

class CustomGeneratorSetup extends GeneratorSetup {

  @Override
  public Configuration getConfig() {
    Configuration config = super.getConfig();
    config.setAPIBuiltinEnabled(true);
    return config;
  }
}
