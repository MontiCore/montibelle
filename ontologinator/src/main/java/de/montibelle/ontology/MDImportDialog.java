package de.montibelle.ontology;

import org.apache.commons.io.FilenameUtils;

import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Path;
import java.util.Optional;

import static de.montibelle.ontology.MDImportAction.reportName;

public class MDImportDialog extends JFrame {

  File file;

  protected void setFile(File file) {
    this.file = file;
  }

  public File getFile() {
    return file;
  }

  public static Optional<MDImportDialog> openDialog() {
    JFileChooser fileChooser = new JFileChooser();
    fileChooser.setDialogTitle("Load ontology from " + reportName);
    fileChooser.setFileSelectionMode(JFileChooser.FILES_ONLY);
    fileChooser.setFileFilter(new FileFilter() {
      @Override
      public boolean accept(File f) {
        return true;
      }

      @Override
      public String getDescription() {
        return reportName;
      }
    });
    fileChooser.setAcceptAllFileFilterUsed(true);

    MDImportDialog context = new MDImportDialog();

    int userSelection = fileChooser.showOpenDialog(context);
    context.setFile(fileChooser.getSelectedFile());

    if (userSelection == JFileChooser.APPROVE_OPTION) {
      return Optional.of(context);
    }
    if (userSelection == JFileChooser.ERROR_OPTION) {
      new MDImportDialog().dialError("ERROR_OPTION returned");
    }
    return Optional.empty();
  }

  public void dialSuccess() {
    JOptionPane.showMessageDialog(
        this.getContentPane(),
        "Successfully imported " + reportName + " from " +
            getFile().getName(),
        "Successful import", JOptionPane.INFORMATION_MESSAGE
    );
  }

  public void dialError(String message) {
    JOptionPane.showMessageDialog(
        this.getContentPane(),
        "An error occurred: " + message,
        "Error occurred",
        JOptionPane.ERROR_MESSAGE);
  }

  public void writeToFile(Path target, String code) {
    target.getParent().toFile().mkdirs();
    try (FileWriter writer = new FileWriter(target.toFile(), false)) {
      writer.write(code);
    } catch (IOException e) {
      this.dialError("IOException: " + e.getMessage());
    }
  }

}
