package de.montibelle.ontology;

import com.nomagic.magicdraw.actions.MDAction;

import java.awt.event.ActionEvent;

public class MDImportAction extends MDAction
{

  public static final String reportName = "Ontology File";

  public MDImportAction()
  {
    super("IMPORT_ONTOLOGY", reportName, null, null);
  }

  @Override
  public void actionPerformed(ActionEvent e)
  {
    MDImportDialog.openDialog().ifPresent(dialog -> {
      var importer = new Importer(dialog.getFile());
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