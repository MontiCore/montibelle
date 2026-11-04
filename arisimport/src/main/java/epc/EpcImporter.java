package epc;

import com.nomagic.uml2.ext.magicdraw.activities.mdintermediateactivities.CentralBufferNode;
import epc._ast.*;
import epc._symboltable.ObjectSymbol;
import epc._visitor.EPCVisitor2;
import com.nomagic.magicdraw.core.Application;
import com.nomagic.magicdraw.core.Project;
import com.nomagic.magicdraw.openapi.uml.ModelElementsManager;
import com.nomagic.magicdraw.openapi.uml.PresentationElementsManager;
import com.nomagic.magicdraw.openapi.uml.ReadOnlyElementException;
import com.nomagic.magicdraw.openapi.uml.SessionManager;
import com.nomagic.magicdraw.uml.symbols.PresentationElement;
import com.nomagic.magicdraw.uml.symbols.layout.composite.CompositeStructureDiagramLayouter;
import com.nomagic.magicdraw.uml.symbols.shapes.NoteView;
import com.nomagic.magicdraw.uml.symbols.shapes.ShapeElement;
import com.nomagic.uml2.ext.magicdraw.activities.mdbasicactivities.ControlNode;
import com.nomagic.uml2.ext.magicdraw.activities.mdfundamentalactivities.Activity;
import com.nomagic.uml2.ext.magicdraw.activities.mdfundamentalactivities.ActivityNode;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.Diagram;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.Element;
import de.monticore.ast.ASTNode;
import de.monticore.symboltable.modifiers.AccessModifier;
import de.se_rwth.commons.logging.Log;

import java.awt.*;
import java.io.File;
import java.io.IOException;
import java.util.*;
import java.util.List;
import java.util.function.Predicate;

import static epc.ASTIncomingUtils.*;

public class EpcImporter {

  public static final String SYSML_AD = "SysML Activity Diagram";

  protected Map<ASTNode, Element> astToElement
      = new HashMap<>();

  protected Map<ASTNode, PresentationElement> astToPresentation
      = new HashMap<>();

  private File file;

  private List<Diagram> diagrams;

  private Optional<String> errorMessage = Optional.empty();

  public EpcImporter(File file) {
    this.file = file;
  }

  public boolean doImport() {
    this.errorMessage = Optional.empty();

    var processed = this.file.toPath().getParent().resolve(
        "Preprocessed_" + file.getName());
    try {
      var preprocessor = new Preprocessor(this.file.toPath(), processed);
      preprocessor.run();
    }
    catch (IOException e) {
      this.errorMessage = Optional.of(e.getMessage());
      return false;
    }

    var tool = new EPCTool();
    EPCMill.init();
    var untangled = this.file.toPath().getParent().resolve(
        "Untangled_" + file.getName());
    Untangler.untangle(tool, processed, untangled);

    this.file = untangled.toFile();

    var ast = tool.parse(this.file.getAbsolutePath());
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    var project = getOrCreateProject();

    SessionManager.getInstance().createSession(project, "Create a diagram");

    diagrams = new ArrayList<>();
    for(var astDiagram : ast.getDiagramList()) {
      var diagram = createDiagram(project, astDiagram);

      ShapeElement shape;
      for(var object : astDiagram.getObjects().getObjectList()) {
        switch (object.getType()) {
          case "Product/Service":
            shape = createObject(project, diagram, object);
            shape.setFillColor(Color.decode("#CE9E3F"));
            break;
          case "Information carrier":
            shape = createObject(project, diagram, object);
            shape.setFillColor(Color.decode("#A0A0A0"));
            break;
          case "Cluster/Data model":
            shape = createObject(project, diagram, object);
            shape.setFillColor(Color.decode("#D36CFF"));
            break;
          case "Role":
            shape = createObject(project, diagram, object);
            shape.setFillColor(Color.decode("#FFFF00"));
            break;
          case "System":
            shape = createObject(project, diagram, object);
            shape.setFillColor(Color.decode("#35A0FF"));
            break;
          case "Event":
            shape = createEventAcceptAction(project, diagram, object);
            shape.setFillColor(Color.decode("#FFB0B0"));
            break;
          case "Function":
            if(object.isPresentDescription()
                && object.getDescription().getName().equals("Interface")) {
              shape = createAction(project, diagram, object);
              shape.setFillColor(Color.decode("#EBEBD8"));
              break;
            }
            else {
              shape = createAction(project, diagram, object);
              shape.setFillColor(Color.decode("#39DA00"));
              break;
            }
          case "Rule":
            createDecision(project, diagram, object);
            break;
          case "Text annotation":
            createAnnotation(project, diagram, object);
            break;
        }
      }

      for(var object : astDiagram.getObjects().getObjectList()) {
        createAssociations(project, diagram, object);
      }

      diagrams.add(diagram);
    }

    boolean res;
    if(this.isPresentErrorMessage()) {
      SessionManager.getInstance().cancelSession(project);
      res = false;
    }
    else {
      SessionManager.getInstance().closeSession(project);
      res = true;
    }

    for(var diagram : diagrams) {
      var diagramPresentation = project.getDiagram(diagram);
      diagramPresentation.open();
      diagramPresentation.layout(false,
          new CompositeStructureDiagramLayouter());
    }

    return res;
  }

  public boolean isPresentErrorMessage() {
    return this.errorMessage.isPresent();
  }

  void setErrorMessage(String error) {
    this.errorMessage = Optional.of(error);
  }

  public String getErrorMessage() {
    return this.errorMessage.get();
  }

  public List<Diagram> getDiagrams() {
    return this.diagrams;
  }

  public static Project getOrCreateProject() {
    var manager = Application.getInstance().getProjectsManager();
    var project = manager.getActiveProject();
    if(project == null) {
      project = manager.createProject();
    }
    return project;
  }

  protected Activity getOrCreateActivity(
      Project project,
      String name)
  {
    var optAct = resolveActivity(project, name);

    if(optAct.isPresent()) {
      return optAct.get();
    }
    else {
      var mem = ModelElementsManager.getInstance();
      var parent = project.getPrimaryModel();

      var activity = project.getElementsFactory().createActivityInstance();
      activity.setName(name);

      try {
        mem.addElement(activity, parent);
      } catch (ReadOnlyElementException e) {
        this.setErrorMessage("Failed to create activity, project was read-only");
        Log.error("0x10104 " + this.getErrorMessage(), e);
      }

      return activity;
    }
  }

  public ShapeElement createAction(
      Project project,
      Diagram diagram,
      ASTObject astObject)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var activity = getOrCreateActivity(project, astObject.getName().replace("%2E", "."));

    var action = project.getElementsFactory().createCallBehaviorActionInstance();
    action.setName(astObject.getName().replace("%2E", "."));
    action.setBehavior(activity);
    astToElement.put(astObject, action);

    try {
      mem.addElement(action, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create activity, project was read-only");
      Log.error("0x10105 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(action, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add action, diagram was read-only");
      Log.error("0x10106 " + this.getErrorMessage(), e);
    }

    return actionShape;
  }

  private ShapeElement createAnnotation(
      Project project,
      Diagram diagram,
      ASTObject node)
  {
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    ShapeElement noteShape = null;
    try {
      noteShape = pem.createNote(dpe);
      ((NoteView)noteShape).setName(node.getName().replace("%2E", "."));
      astToPresentation.put(node, noteShape);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add note, diagram was read-only");
      Log.error("0x10109 " + this.getErrorMessage(), e);
    }

    return noteShape;
  }

  private void createAssociations(
      Project project,
      Diagram diagram,
      ASTObject object)
  {
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var visitor = new EPCVisitor2() {
      @Override
      public void visit(ASTAssociation otherRef) {
        Predicate<ObjectSymbol> p = obj -> obj.isPresentAstNode() &&
            obj.getAstNode().getType().equals(otherRef.getType());
        var other = otherRef.getEnclosingScope()
            .resolveObjectMany(otherRef.getName(), AccessModifier.ALL_INCLUSION, p)
            .get(0).getAstNode();

        PresentationElement otherPresentation;
        PresentationElement thisPresentation;

        if(otherRef.getType().equals("Text annotation")) {
          otherPresentation = astToPresentation.get(other);

          var thisElement = astToElement.get(object);
          thisPresentation = dpe
              .findPresentationElement(thisElement, PresentationElement.class);
        }
        else if(object.getType().equals("Text annotation")) {
          return;
        }
        else {
          setErrorMessage(
              "Encountered an association where neither end was a note");
          Log.error("0x10113 " + getErrorMessage(),
              otherRef.get_SourcePositionStart());
          return;
        }

        try {
          if (otherPresentation instanceof NoteView) {
            pem.connectNote((ShapeElement) otherPresentation, thisPresentation);
          } else if (thisPresentation instanceof NoteView) {
            pem.connectNote((ShapeElement) thisPresentation, otherPresentation);
          }
          else {
            Log.warn("0x10101 Could not process annotation, neither end was a a note",
                otherRef.get_SourcePositionStart());
          }
        }
        catch (ReadOnlyElementException e) {
          setErrorMessage(
              "Failed to link note to milestone, diagram was read-only");
          Log.error("0x10102 " + getErrorMessage(), e);
        }
      }

      private List<String> alreadyProcessed = new ArrayList<>();

      @Override
      public void visit(ASTIncoming sourceRef) {
        var siblings = getSiblingsWhoReferenceSameObject(sourceRef);
        if (siblings.size() > 0
            && !alreadyProcessed.contains(sourceRef.getName()))
        {
          alreadyProcessed.add(sourceRef.getName());
          var sources = getSources(sourceRef);
          if (sources.size() == siblings.size() + 1) {
            for(var source : sources) {
              incomingHelper(source);
            }
          }
          else {
            Log.error("0x10120 Multiple incoming relationships share a name, " +
                    "but the number of relationships does not match the " +
                    "number of potential sources!",
                sourceRef.get_SourcePositionStart(),
                sourceRef.get_SourcePositionEnd());
          }
        }
        else if (siblings.size() == 0) {
          incomingHelper(getSource(sourceRef));
        }
      }
      private void incomingHelper(ASTObject source) {
        var sourceElement = astToElement.get(source);
        var sourcePresentation = dpe
            .findPresentationElement(sourceElement, PresentationElement.class);

        var targetElement = astToElement.get(object);
        var targetPresentation = dpe
            .findPresentationElement(targetElement, PresentationElement.class);

        Log.info(String.format(
            "About to create a control flow between %s and %s",
            source.getName(), object.getName()), "EPCVisitor2");
        createControlFlow(project, diagram,
            (ShapeElement) sourcePresentation,
            (ShapeElement) targetPresentation);
      }
      @Override
      public void visit(ASTOutgoing node) {
      }
    };
    var traverser = EPCMill.inheritanceTraverser();
    traverser.add4EPC(visitor);
    object.accept(traverser);
  }

  protected void createControlFlow(
      Project project,
      Diagram diagram,
      ShapeElement from,
      ShapeElement to)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();

    Element flow;
    if(from.getElement() instanceof CentralBufferNode
        || to.getElement() instanceof CentralBufferNode)
    {
      var objectFlow = project.getElementsFactory().createObjectFlowInstance();
      objectFlow.setSource((ActivityNode) from.getElement());
      objectFlow.setTarget((ActivityNode) to.getElement());
      flow = objectFlow;
    }
    else
    {
      var controlFlow = project.getElementsFactory().createControlFlowInstance();
      controlFlow.setSource((ActivityNode) from.getElement());
      controlFlow.setTarget((ActivityNode) to.getElement());
      flow = controlFlow;
    }

    try {
      mem.addElement(flow, diagram.getOwnerOfDiagram());
    } catch (Exception e) {
      this.setErrorMessage("Failed to create control flow, project was read-only");
      Log.error("0x10110 " + this.getErrorMessage(), e);
    }

    try {
      pem.createPathElement(flow, from, to);
    } catch (Exception e) {
      this.setErrorMessage("Failed to add control flow, diagram was read-only");
      Log.error("0x10111 " + this.getErrorMessage(), e);
    }
  }

  private PresentationElement createDecision(
      Project project,
      Diagram diagram,
      ASTObject node)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var incoming = node.getRelationshipList().stream()
        .filter(r -> r instanceof ASTIncoming)
        .count();
    var outgoing = node.getRelationshipList().stream()
        .filter(r -> r instanceof ASTOutgoing)
        .count();

    ControlNode ctrlNode;
    if(incoming > outgoing) {
      ctrlNode = project.getElementsFactory().createMergeNodeInstance();
    }
    else {
      ctrlNode = project.getElementsFactory().createDecisionNodeInstance();
    }


    try {
      mem.addElement(ctrlNode, diagram.getOwnerOfDiagram());
      astToElement.put(node, ctrlNode);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to create decision node, project was read-only");
      Log.error("0x10107 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(ctrlNode, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to add decision node, diagram was read-only");
      Log.error("0x10108 " + this.getErrorMessage(), e);
    }

    return actionShape;
  }

  public Diagram createDiagram(Project project, ASTDiagram node)
  {
    var mem = ModelElementsManager.getInstance();

    var activity = getOrCreateActivity(project, node.getName().replace("%2E", "."));

    Diagram diagram = null;
    try {
      diagram = mem.createDiagram(SYSML_AD, activity);
      astToElement.put(node, diagram);
    }
    catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create diagram, project was read-only");
      Log.error("0x10103 " + this.getErrorMessage(), e);
    }
    return diagram;
  }

  public ShapeElement createEventAcceptAction(
      Project project,
      Diagram diagram,
      ASTObject astObject)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var action = project.getElementsFactory().createAcceptEventActionInstance();
    action.setName(astObject.getName().replace("%2E", "."));
    astToElement.put(astObject, action);

    try {
      mem.addElement(action, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create activity, project was read-only");
      Log.error("0x10105 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(action, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add action, diagram was read-only");
      Log.error("0x10106 " + this.getErrorMessage(), e);
    }

    return actionShape;
  }

  private void createStartFinal(
      Project project,
      Diagram diagram,
      ASTObject object)
  {
    Predicate<ASTObject> hasIncoming = o -> o.getRelationshipList().stream()
        .anyMatch(r -> r instanceof ASTIncoming);
    Predicate<ASTObject> hasOutgoing = o -> o.getRelationshipList().stream()
        .anyMatch(r -> r instanceof ASTOutgoing);

    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);
    var mem = ModelElementsManager.getInstance();

    ControlNode node;
    if(hasIncoming.and(hasOutgoing.negate()).test(object)) {
      node = project.getElementsFactory().createActivityFinalNodeInstance();
    }
    else if(hasIncoming.negate().and(hasOutgoing).test(object)) {
      node = project.getElementsFactory().createInitialNodeInstance();
    }
    else {
      setErrorMessage("Encountered event that was neither start nor end event");
      Log.error("0x10114 " + getErrorMessage(),
          object.get_SourcePositionStart());
      return;
    }
    astToElement.put(object, node);

    try {
      mem.addElement(node, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to create control node, diagram was read-only");
      Log.error("0x10115 " + this.getErrorMessage(), e);
    }

    ShapeElement shape = null;
    try {
      shape = pem.createShapeElement(node, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to add control node, diagram was read-only");
      Log.error("0x10116 " + this.getErrorMessage(), e);
    }
  }

  private ShapeElement createObject(
      Project project,
      Diagram diagram,
      ASTObject astObject)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var object = project.getElementsFactory().createCentralBufferNodeInstance();
    object.setName(astObject.getName().replace("%2E", "."));
    astToElement.put(astObject, object);

    try {
      mem.addElement(object, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create activity, project was read-only");
      Log.error("0x10118 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(object, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add action, diagram was read-only");
      Log.error("0x10119 " + this.getErrorMessage(), e);
    }

    return actionShape;

  }

  public static Optional<Activity> resolveActivity(
      Project project,
      String name)
  {
    Optional<Activity> res = Optional.empty();

    ArrayList children = new ArrayList();
    Element current = project.getPrimaryModel();
    children.add(current);
    for (int i = 0; i < children.size(); i++)
    {
      current = (Element) children.get(i);

      if(current instanceof Activity
          && ((Activity)current).getName().equals(name))
      {
        res = Optional.of((Activity) current);
        break;
      }

      children.addAll(current.getOwnedElement());
    }

    return res;
  }

}
