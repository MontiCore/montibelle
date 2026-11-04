package montibelle.focus._ast;

import montibelle.transformer.generic.sessions.DocumentFiles;
import montibelle.transformer.generic.sessions.ExportFiles;
import montibelle.transformer.generic.sessions.Options;
import montibelle.transformer.generic.sessions.Theories;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

public class ASTSession extends ASTSessionTOP {
  protected String chapter = null;
  protected String parent = "data_inc";
  protected String dir = null;
  protected String description = null;
   protected List<String> groups = new ArrayList<>(List.of("generated"));
   protected List<Options> options = new ArrayList<>();
   protected List<String> importSessions = new ArrayList<>();
   protected List<Theories> theories = new ArrayList<>();
  protected List<DocumentFiles> documentFiles = new ArrayList<>();
  protected List<ExportFiles> exportFiles = new ArrayList<>();

  public String getChapter() {
    return chapter;
  }

  public void setChapter(String chapter) {
    this.chapter = chapter;
  }

  public String getParent() {
    return parent;
  }

  public void setParent(String parent) {
    this.parent = parent;
  }

  public String getDir() {
    return dir;
  }

  public void setDir(String dir) {
    this.dir = dir;
  }

  public String getDescription() {
    return description;
  }

  public void setDescription(String description) {
    this.description = description;
  }

  public List<String> getGroups() {
    return groups;
  }

  public void setGroups(List<String> groups) {
    this.groups = groups;
  }

  public List<Options> getOptions() {
    return options;
  }

  public void setOptions(List<Options> options) {
    this.options = options;
  }

  public List<String> getImportSessions() {
    return importSessions;
  }

  public void setImportSessions(List<String> importSessions) {
    this.importSessions = importSessions;
  }

  public List<Theories> getTheories() {
    return theories;
  }

  public void setTheories(List<Theories> theories) {
    this.theories = theories;
  }

  public List<DocumentFiles> getDocumentFiles() {
    return documentFiles;
  }

  public void setDocumentFiles(List<DocumentFiles> documentFiles) {
    this.documentFiles = documentFiles;
  }

  public List<ExportFiles> getExportFiles() {
    return exportFiles;
  }

  public void setExportFiles(List<ExportFiles> exportFiles) {
    this.exportFiles = exportFiles;
  }

  public Path getPath() {
    if (!isEmptyPath()) {
      List<String> pathList = getPathList();
      return Path.of(pathList.get(0), pathList.subList(1, sizePath()).toArray(new String[0]));
    } else {
      throw new IllegalStateException("Path for session " + getName() + " is empty");
    }
  }

  public void addGroup(String group) {
    groups.add(group);
  }

  public void addOption(Options option) {
    options.add(option);
  }

  public void addImportSession(String importSession) {
    importSessions.add(importSession);
  }

  public void addDocumentFiles(DocumentFiles documentFile) {
    documentFiles.add(documentFile);
  }

  public void addExportFiles(ExportFiles exportFile) {
    exportFiles.add(exportFile);
  }

  public void addTheory(Theories theory) {
    theories.add(theory);
  }

  @Override
  public boolean equals(Object other) {
    return deepEquals(other);
  }

  @Override
  public int hashCode() {
    return getName().hashCode();
  }

  @Override
  public String toString() {
    return getName();
  }
}
