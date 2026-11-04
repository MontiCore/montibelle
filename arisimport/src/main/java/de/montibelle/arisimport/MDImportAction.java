package de.montibelle.arisimport;

import com.nomagic.magicdraw.actions.MDAction;
import epc.EpcImporter;

import java.awt.event.ActionEvent;

public class MDImportAction extends MDAction
{

  public static final String reportName = "ARIS Model Information Report";

  public MDImportAction()
  {
    super("IMPORT_ARIS", reportName, null, null);
  }

  @Override
  public void actionPerformed(ActionEvent e)
  {
    MDImportDialog.openDialog().ifPresent(dialog -> {
      var importer = new EpcImporter(dialog.getFile());
      if(importer.doImport()) {
        dialog.dialSuccess();
      }
      else if (importer.isPresentErrorMessage()) {
        dialog.dialError(importer.getErrorMessage());
      }
      else {
        dialog.dialError("An unknown error occurred");
      }
    });
  }

}
