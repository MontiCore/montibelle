package epc._prettyprint;

import de.monticore.prettyprint.IndentPrinter;
import epc._ast.*;

import static epc.Preprocessor.wrap;

public class EPCPrettyPrinter extends EPCPrettyPrinterTOP {
  public EPCPrettyPrinter(IndentPrinter printer, boolean printComments) {
    super(printer, printComments);
  }

  @Override
  public void handle(ASTEmail node) {
    getPrinter().print("yajol76145@hutudns.com\n");
  }

  @Override
  public void handle (ASTModelInformation node) {
    getPrinter().print("Model information\n");
    getPrinter().print("Date: ");
    node.getDate().accept(getTraverser());
    getPrinter().print("\n");
    if (node.isPresentName() ) {
      getPrinter().print("Model: ");
      getPrinter().print(wrap(node.getName()) + "\n");
    }
  }

  @Override
  public void handle(ASTDiagram node) {
    getPrinter().print(wrap(node.getName()) + "\n");
    node.getProperties().accept(getTraverser());

    node.getObjects().accept(getTraverser());

    node.getGraphic().accept(getTraverser());
    getPrinter().print("\n");
  }

  @Override
  public void handle(ASTProperties node) {
    getPrinter().print("Properties");
    getPrinter().print("\n");
    getPrinter().print("Properties");
    getPrinter().print("\n");
    getPrinter().print("Type                                                 ");
    getPrinter().print(wrap(node.getType()) + "\n");
    getPrinter().print("Group                                                ");
    getPrinter().print(wrap(node.getGroup()) + "\n");
    if (node.isPresentDescription()) {
      node.getDescription().accept(getTraverser());
    }
    getPrinter().print("Time of generation                                   ");
    node.getGeneration().accept(getTraverser());
    getPrinter().print("\n");
    getPrinter().print("Creator                                              ");
    node.getCreator().accept(getTraverser());

    getPrinter().print("Last change                                          ");
    node.getChange().accept(getTraverser());
    getPrinter().print("\n");
    getPrinter().print("Last user                                            ");
    node.getLastUser().accept(getTraverser());
  }

  @Override
  public void handle (ASTDescription node) {
    getPrinter().print("Description/Definition                               ");
    getPrinter().print(wrap(node.getName()) + "\n");
  }

  @Override
  public void handle(ASTObjects node) {
    getPrinter().print("Objects\n");
    node.getObjectList().forEach(n->n.accept(getTraverser()));
  }

  @Override
  public void handle(ASTObject node) {
    getPrinter().print(wrap(node.getName()) + "\n");
    getPrinter().print("Properties\n");
    getPrinter().print("Type                                                 ");
    getPrinter().print(wrap(node.getType()) + "\n");
    getPrinter().print("Group                                                ");
    getPrinter().print(wrap(node.getGroup()) + "\n");
    if (node.isPresentDescription()) {
      node.getDescription().accept(getTraverser());
    }
    if (node.isPresentTitle()) {
      node.getTitle().accept(getTraverser());
    }
    if (node.isPresentLink()) {
      node.getLink().accept(getTraverser());
    }
    getPrinter().print("Time of generation                                   ");
    node.getGeneration().accept(getTraverser());
    getPrinter().print("\n");
    getPrinter().print("Creator                                              ");
    node.getCreator().accept(getTraverser());
    getPrinter().print("Last change                                          ");
    node.getChange().accept(getTraverser());
    getPrinter().print("\n");
    getPrinter().print("Last user                                            ");
    node.getLastUser().accept(getTraverser());
    getPrinter().print("Relationships\n");
    getPrinter().print("Relationship type     Object name     Object type\n");
    node.getRelationshipList().forEach(n->n.accept(getTraverser()));
  }

  @Override
  public void handle(ASTTitle node) {
    getPrinter().print("Title 1                                              ");
    getPrinter().print(wrap(node.getName()) + "\n");
  }

  @Override
  public void handle(ASTLink node) {
    getPrinter().print("Link 1                                              ");
    getPrinter().print(wrap(node.getName()) + "\n");
  }

  @Override
  public void handle(ASTOutgoing node) {
    if (node.isActivates()) {
      getPrinter().print("activates");
    } else if (node.isLeads_to()) {
      getPrinter().print("leads_to");
    } else if (node.isCreates()) {
      getPrinter().print("creates");
    } else if (node.isIs_predecessor_of()) {
      getPrinter().print("is_predecessor_of");
    } else if (node.isIs_input_for()) {
      getPrinter().print("is_input_for");
    } else if (node.isProvides_input_for()) {
      getPrinter().print("provides_input_for");
    } else if (node.isDefines_status()) {
      getPrinter().print("defines_status");
    } else if (node.isLinks()) {
      getPrinter().print("links");
    } else if (node.isSupports()) {
      getPrinter().print("supports");
    } else if (node.isHas_as_output()) {
      getPrinter().print("has_as_output");
    } else if (node.isHas_consulting_role_in()) {
      getPrinter().print("has_consulting_role_in");
    } else if (node.isMust_be_informed_about()) {
      getPrinter().print("must_be_informed_about");
    } else if (node.isIs_responsible_for()) {
      getPrinter().print("is_responsible_for");
    } else if (node.isIs_accountable_for()) {
      getPrinter().print("is_accountable_for");
    } else if (node.isIs_evaluated_by()) {
      getPrinter().print("is_evaluated_by");
    }
    getPrinter().print("  " + wrap(node.getName()) + "  " + wrap(node.getType()) + "\n");
  }

  @Override
  public void handle(ASTIncoming node) {
    if (node.isIs_defined()) {
      getPrinter().print("is_defined");
    } else if (node.isIs_activated_by()) {
      getPrinter().print("is_activated_by");
    } else if (node.isEvaluates()) {
      getPrinter().print("evaluates");
    } else if (node.isIs_linked_by()) {
      getPrinter().print("is_linked_by");
    } else if (node.isIs_assigned_to()) {
      getPrinter().print("is_assigned_to");
    } else if (node.isIs_created_by()) {
      getPrinter().print("is_created_by");
    } else if (node.isFollows()) {
      getPrinter().print("follows");
    } else if (node.isIs_dependent_on()) {
      getPrinter().print("is_dependent_on");
    } else if (node.isHas_as_input()) {
      getPrinter().print("has_as_input");
    } else if (node.isIs_supported_by_consulting_role_of()) {
      getPrinter().print("is_supported_by_consulting_role_of");
    } else if (node.isIs_supported_by()) {
      getPrinter().print("is_supported_by");
    } else if (node.isReceives_input_from()) {
      getPrinter().print("receives_input_from");
    } else if (node.isIs_under_responsibility_of()) {
      getPrinter().print("is_under_responsibility_of");
    } else if (node.isIs_output_of()) {
      getPrinter().print("is_output_of");
    } else if (node.isIs_decided_by()) {
      getPrinter().print("is_decided_by");
    } else if (node.isResult_is_forwarded_to()) {
      getPrinter().print("result_is_forwarded_to");
    }
    getPrinter().print("  " + wrap(node.getName()) + "  " + wrap(node.getType()) + "\n");
  }
}
