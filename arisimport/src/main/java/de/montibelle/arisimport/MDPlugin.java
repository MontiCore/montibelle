package de.montibelle.arisimport;

import com.nomagic.magicdraw.actions.ActionsConfiguratorsManager;

public class MDPlugin extends com.nomagic.magicdraw.plugins.Plugin {

  @Override
  public void init() {
    ActionsConfiguratorsManager
        .getInstance()
        .addMainMenuConfigurator(new MDMainMenuConfigurator(new MDImportAction()));
  }

  @Override
  public boolean close() {
    return true;
  }

  @Override
  public boolean isSupported() {
    return true;
  }

}