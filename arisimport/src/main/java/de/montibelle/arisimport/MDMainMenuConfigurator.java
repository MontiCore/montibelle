package de.montibelle.arisimport;

import com.nomagic.actions.AMConfigurator;
import com.nomagic.actions.ActionsCategory;
import com.nomagic.actions.ActionsManager;
import com.nomagic.actions.NMAction;
import com.nomagic.magicdraw.actions.MDActionsCategory;
import de.se_rwth.commons.logging.Log;

public class MDMainMenuConfigurator implements AMConfigurator
{

  private boolean initialized = false;

  String FILE = "FILE";

  private final NMAction action;

  public MDMainMenuConfigurator(NMAction action)
  {
    this.action = action;
  }

  @Override
  public void configure(ActionsManager manager)
  {
    if(!initialized || true) {
      ActionsCategory category = manager.getActionsCategoryRecursively(manager.getCategories(), "IMPORT_CATEGORY");

      if (category == null) {
        Log.warn(
            "0x10112 The menu item \"Import from...\" could not be found.");
        category = new MDActionsCategory(FILE, FILE);
        category.setNested(true);
        manager.addCategory(category);
      }

      category.addAction(action);
      initialized = true;
    }
  }

  @Override
  public int getPriority()
  {
    return AMConfigurator.MEDIUM_PRIORITY;
  }

}