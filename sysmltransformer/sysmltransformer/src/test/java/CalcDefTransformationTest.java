import de.monticore.lang.sysmlactions._ast.ASTCalcDef;
import de.monticore.lang.sysmlactions._visitor.SysMLActionsVisitor2;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.monticore.lang.sysmlv2.types3.SysMLTypeCheck3;
import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbol;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusTool;
import montibelle.transformer.sysml.printer.TypePrinter;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import static cc2focus.OOTypeSymbol2FocusType.buildStruct;
import static org.assertj.core.api.Assertions.assertThat;

public class CalcDefTransformationTest {

  @Test
  public void testAddCalcDefTransformer() throws IOException {
    var model = "calc def add {\n" +
        "  in a: nat;\n" +
        "  in b: nat;\n" +
        "  return : nat;\n" +
        "\n" +
        "  a + b\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo("fun add(a: nat, b: nat) nat = \"(a + b)\"");
  }

  @Test
  public void testReachableStatesCalcDefTransformer() throws IOException {
    var model = "calc def ReachableStates {\n" +
        "  in c: Controller;\n" +
        "  in input: Signal[*];\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var parseResult = SysMLv2Mill.parser().parse_StringSysMLModel(model);
    assertThat(parseResult).isPresent();
    var ast = parseResult.get();

    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo("fun ReachableStates(c: Controller, input: Signal set)  = \"\"");
  }

  @Test
  public void testPossibleSwitchCalcDefTransformer() throws IOException {
    var dependency = "attribute def Access_Point {\n" +
        "  enum sect: Section;\n" +
        "}";
    var model = "calc def Possible_Switch {\n" +
        "  in a: Access_Point;\n" +
        "  in b: Access_Point;\n" +
        "  return : Boolean;\n" +
        "\n" +
        "  a.sect == b.sect \n" +
        "      & (a,b) != (a42,a43)\n" +
        "      & (a,b) != (a43,a42)\n" +
        "      & (a,b) != (a72,a71)\n" +
        "      & (a,b) != (a71,a72)\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(dependency).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
            "fun Possible_Switch(a: Access_Point, b: Access_Point) Boolean = " +
                "\"((((((Access_Point_get_sect a) = (Access_Point_get_sect b)) " +
                "\\<and> ((a,b) \\<noteq> (a42,a43))) \\<and> ((a,b) " +
                "\\<noteq> (a43,a42))) \\<and> ((a,b) \\<noteq> (a72,a71))) " +
                "\\<and> ((a,b) \\<noteq> (a71,a72)))\"");
  }

  @Test
  public void testIsFreeCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "  enum s3;\n" +
            "  enum s4;\n" +
            "  enum s5;\n" +
            "  enum s6;\n" +
            "  enum s7;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "calc def IsFree {\n" +
            "  in trains: Train[*];\n" +
            "  in a: Access_Point;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  trains->forAll {\n" +
            "    in train: Train;\n" +
            "    train.position.sect != a.sect\n" +
            "  }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint =
        (OOTypeSymbol) gs.resolveType("Access_Point").get();

    var train =
        (OOTypeSymbol) gs.resolveType("Train").get();

    var accessPointStruct =
        buildStruct(accessPoint, new TypePrinter());

    var trainStruct =
        buildStruct(train, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
            "fun IsFree(trains: Train set, a: Access_Point) Boolean = \"Ball trains (\\<lambda> train. ((Access_Point_get_sect (Train_get_position train)) \\<noteq> (Access_Point_get_sect a)))\"");
  }

  @Test
  public void testProtectedCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "  enum s3;\n" +
            "  enum s4;\n" +
            "  enum s5;\n" +
            "  enum s6;\n" +
            "  enum s7;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "calc def Protected {\n" +
            "  in railway: Railway_Network;\n" +
            "  in s: Section;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  (railway.access_points)->forAll {\n" +
            "    in a: Access_Point;\n" +
            "    a.sect == s implies not a.isGreen & not a.co.isGreen\n" +
            "  }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
            "fun Protected(railway: Railway_Network, s: Section) Boolean = \"Ball ((Railway_Network_get_access_points railway)) (\\<lambda> a. ((Access_Point_get_sect a) = s) \\<longrightarrow> (\\<not>((Access_Point_get_isGreen a)) \\<and> \\<not>((Access_Point_get_isGreen (Access_Point_get_co a)))))\"");
  }

  @Test
  public void testCloseCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "calc def Close {\n" +
            "  in a: Access_Point;\n" +
            "  in b: Access_Point;\n" +
            "  in railway: Railway_Network;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  a.sect == b.sect\n" +
            "  | (railway.access_points)->exists {\n" +
            "      in c: Access_Point;\n" +
            "      a.sect == c.co.sect & c.sect == b.sect\n" +
            "    }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        focusModels.add(CalcDefTransformer.transform(node));
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
      "fun Close(a: Access_Point, b: Access_Point, railway: Railway_Network)"
          + " Boolean = \"(((Access_Point_get_sect a) = (Access_Point_get_sect b)) "
          + "\\<or> Bex ((Railway_Network_get_access_points railway)) "
          + "(\\<lambda> c. (((Access_Point_get_sect a) = (Access_Point_get_sect "
          + "(Access_Point_get_co c))) \\<and> ((Access_Point_get_sect c) = "
          + "(Access_Point_get_sect b)))))\""
        );
  }

  @Test
  public void testSecureStateCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "  enum s3;\n" +
            "  enum s4;\n" +
            "  enum s5;\n" +
            "  enum s6;\n" +
            "  enum s7;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "calc def Close {\n" +
            "  in a: Access_Point;\n" +
            "  in b: Access_Point;\n" +
            "  in railway: Railway_Network;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  a.sect == b.sect\n" +
            "  | (railway.access_points)->exists {\n" +
            "      in c: Access_Point;\n" +
            "      a.sect == (c.co).sect & c.sect == b.sect\n" +
            "    }\n" +
            "}\n" +
            "\n" +
            "calc def SecureState {\n" +
            "  in railway: Railway_Network;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  railway.trains->forAll {\n" +
            "    in t1: Train;\n" +
            "    railway.trains->forAll {\n" +
            "      in t2: Train;\n" +
            "      Close(t1.position, t2.position, railway) implies (t1 == t2)\n" +
            "    }\n" +
            "  }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("SecureState")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
            "fun SecureState(railway: Railway_Network) Boolean = \"Ball"
                + " (Railway_Network_get_trains railway) (\\<lambda> t1. Ball "
                + "(Railway_Network_get_trains railway) (\\<lambda> t2. (Close "
                + "(Train_get_position t1) (Train_get_position t2) railway) "
                + "\\<longrightarrow> ((t1 = t2))))\""
        );
  }

  @Test
  public void testSafeLightCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "  enum s3;\n" +
            "  enum s4;\n" +
            "  enum s5;\n" +
            "  enum s6;\n" +
            "  enum s7;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "calc def Close {\n" +
            "  in a: Access_Point;\n" +
            "  in b: Access_Point;\n" +
            "  in railway: Railway_Network;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  a.sect == b.sect\n" +
            "  | (railway.access_points)->exists {\n" +
            "      in c: Access_Point;\n" +
            "      a.sect == (c.co).sect & c.sect == b.sect\n" +
            "    }\n" +
            "}\n" +
            "\n" +
            "calc def SafeLight {\n" +
            "  in railway: Railway_Network;\n" +
            "  in a: Access_Point;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  a.isOpen & a.co.isOpen &\n" +
            "    (railway.access_points)->forAll {\n" +
            "      in b: Access_Point;\n" +
            "      (Close(a, b, railway) & b.isGreen)\n" +
            "        implies (\n" +
            "          a == b | (a.sect == b.co.sect & a.co.sect == b.sect)\n" +
            "        )\n" +
            "    }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("SafeLight")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);
    assertThat(focusModels.get(0))
        .isEqualTo(
            "fun SafeLight(railway: Railway_Network, a: Access_Point) "
                + "Boolean = \"(((Access_Point_get_isOpen a) \\<and> "
                + "(Access_Point_get_isOpen (Access_Point_get_co a))) \\<and> "
                + "Ball ((Railway_Network_get_access_points railway)) "
                + "(\\<lambda> b. (((Close a b railway) \\<and> "
                + "(Access_Point_get_isGreen b))) \\<longrightarrow> (((a = b) "
                + "\\<or> ((((Access_Point_get_sect a) = (Access_Point_get_sect "
                + "(Access_Point_get_co b))) \\<and> ((Access_Point_get_sect "
                + "(Access_Point_get_co a)) = (Access_Point_get_sect b))))))))\""
        );
  }

  @Test
  public void testSafeGreenCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "  enum s3;\n" +
            "  enum s4;\n" +
            "  enum s5;\n" +
            "  enum s6;\n" +
            "  enum s7;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "calc def SafeLight {\n" +
            "  in railway: Railway_Network;\n" +
            "  in a: Access_Point;\n" +
            "  return : Boolean;\n" +
            "  true\n" +
            "}\n" +
            "\n" +
            "calc def Close {\n" +
            "  in a: Access_Point;\n" +
            "  in b: Access_Point;\n" +
            "  in railway: Railway_Network;\n" +
            "  return : Boolean;\n" +
            "  true\n" +
            "}\n" +
            "\n" +
            "calc def IsFree {\n" +
            "  in trains: Train[*];\n" +
            "  in b: Access_Point;\n" +
            "  return : Boolean;\n" +
            "  true\n" +
            "}\n" +
            "\n" +
            "calc def SafeGreen {\n" +
            "  in railway: Railway_Network;\n" +
            "  in a: Access_Point;\n" +
            "  return : Boolean;\n" +
            "\n" +
            "  SafeLight(railway, a)\n" +
            "  & (railway.access_points)->forAll {\n" +
            "    in b: Access_Point;\n" +
            "    Close(a, b, railway) & a.co.sect != b.sect implies IsFree(railway.trains, b)\n" +
            "  }\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("SafeGreen")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels.get(0))
        .isEqualTo(
        "fun SafeGreen(railway: Railway_Network, a: Access_Point) "
            + "Boolean = \"((SafeLight railway a) \\<and> Ball "
            + "((Railway_Network_get_access_points railway)) (\\<lambda> b. "
            + "((Close a b railway) \\<and> ((Access_Point_get_sect "
            + "(Access_Point_get_co a)) \\<noteq> (Access_Point_get_sect b)))"
            + " \\<longrightarrow> (IsFree (Railway_Network_get_trains railway) b)))\""
        );
  }

  @Test
  public void testPhysTransEnterCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "attribute def Enters {\n" +
            "  attribute train: Train;\n" +
            "  attribute access: Access_Point;\n" +
            "}\n" +
            "\n" +
            "calc def Phys_Trans_Enter {\n" +
            "  in railway: Railway_Network;\n" +
            "  in signal: Enters;\n" +
            "  return : Railway_Network;\n" +
            "\n" +
            "  attribute t0: Train = signal.train;\n" +
            "  attribute a: Access_Point = signal.access;\n" +
            "\n" +
            "  attribute untouched: Train[*] = railway.trains->select {\n" +
            "    in t: Train;\n" +
            "    t != t0\n" +
            "  };\n" +
            "\n" +
            "  if a.co.sect == t0.position.sect ?\n" +
            "    new Railway_Network(\n" +
            "      access_points = railway.access_points,\n" +
            "      trains = untouched + new Train(a)\n" +
            "    )\n" +
            "  else\n" +
            "    railway\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();
    var enters = (OOTypeSymbol) gs.resolveType("Enters").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());
    var entersStruct = buildStruct(enters, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    focusTool.createSymbolTable(entersStruct);
    focusTool.completeSymbolTable(entersStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("Phys_Trans_Enter")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);

    assertThat(focusModels.get(0)).isEqualTo(
        "fun Phys_Trans_Enter(railway: Railway_Network, signal: Enters) Railway_Network ="
            + " \"let var_t0 = (Enters_get_train signal); "
            + "var_a = (Enters_get_access signal); "
            + "var_untouched = filter (\\<lambda> t. (t \\<noteq> var_t0)) "
            + "(Railway_Network_get_trains railway) "
            + "in (if ((Access_Point_get_sect (Access_Point_get_co var_a)) = "
            + "(Access_Point_get_sect (Train_get_position var_t0))) then "
            + "(Railway_NetworkConstr (Railway_Network_get_access_points railway) "
            + "(var_untouched + (TrainConstr var_a))) else railway)\"");

  }

  @Test
  public void testPhysTransColorCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "attribute def SetColor {\n" +
            "  attribute access: Access_Point;\n" +
            "  attribute b: boolean;\n" +
            "}\n" +
            "\n" +
            "calc def Phys_Trans_Color {\n" +
            "  in railway: Railway_Network;\n" +
            "  in signal: SetColor;\n" +
            "  return : Railway_Network;\n" +
            "\n" +
            "  attribute access_after: Access_Point = new Access_Point(\n" +
            "    signal.access.sect,\n" +
            "    signal.access.co,\n" +
            "    signal.access.isOpen,\n" +
            "    signal.b\n" +
            "  );\n" +
            "\n" +
            "  attribute coAccess_after: Access_Point = new Access_Point(\n" +
            "    signal.access.co.sect,\n" +
            "    access_after,\n" +
            "    signal.access.co.isOpen,\n" +
            "    signal.access.co.isGreen\n" +
            "  );\n" +
            "\n" +
            "  attribute untouched: Access_Point[*] = railway.access_points->select {\n" +
            "    in a: Access_Point;\n" +
            "    a != signal.access & a != signal.access.co\n" +
            "  };\n" +
            "\n" +
            "  new Railway_Network(\n" +
            "    access_points = untouched + (access_after, coAccess_after),\n" +
            "    trains = railway.trains\n" +
            "  )\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();
    var setColor = (OOTypeSymbol) gs.resolveType("SetColor").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());
    var setColorStruct = buildStruct(setColor, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    focusTool.createSymbolTable(setColorStruct);
    focusTool.completeSymbolTable(setColorStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("Phys_Trans_Color")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);

    assertThat(focusModels.get(0)).isEqualTo(
        "fun Phys_Trans_Color(railway: Railway_Network, signal: SetColor) Railway_Network ="
            + " \"let var_access_after = (Access_PointConstr "
            + "(Access_Point_get_sect (SetColor_get_access signal)) "
            + "(Access_Point_get_co (SetColor_get_access signal)) "
            + "(Access_Point_get_isOpen (SetColor_get_access signal)) "
            + "(SetColor_get_b signal)); "
            + "var_coAccess_after = (Access_PointConstr "
            + "(Access_Point_get_sect (Access_Point_get_co (SetColor_get_access signal))) "
            + "var_access_after "
            + "(Access_Point_get_isOpen (Access_Point_get_co (SetColor_get_access signal))) "
            + "(Access_Point_get_isGreen (Access_Point_get_co (SetColor_get_access signal)))); "
            + "var_untouched = filter (\\<lambda> a. "
            + "((a \\<noteq> (SetColor_get_access signal)) \\<and> "
            + "(a \\<noteq> (Access_Point_get_co (SetColor_get_access signal))))) "
            + "(Railway_Network_get_access_points railway) "
            + "in (Railway_NetworkConstr "
            + "(var_untouched + (var_access_after,var_coAccess_after)) "
            + "(Railway_Network_get_trains railway))\"");
  }

  @Test
  public void testPhysTransOpenCalcDefTransformer() throws IOException {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute co: Access_Point;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n" +
            "\n" +
            "attribute def Train {\n" +
            "  attribute position: Access_Point;\n" +
            "}\n" +
            "\n" +
            "attribute def Railway_Network {\n" +
            "  attribute access_points: Access_Point[*];\n" +
            "  attribute trains: Train[*];\n" +
            "}\n" +
            "\n" +
            "attribute def OpenUp {\n" +
            "  attribute a: Access_Point;\n" +
            "  attribute b: Access_Point;\n" +
            "}\n" +
            "\n" +
            "calc def Possible_Switch {\n" +
            "  in a: Access_Point;\n" +
            "  in b: Access_Point;\n" +
            "  return : Boolean;\n" +
            "  a == b\n" +
            "}\n" +
            "\n" +
            "calc def Phys_Trans_Open {\n" +
            "  in railway: Railway_Network;\n" +
            "  in signal: OpenUp;\n" +
            "  return : Railway_Network;\n" +
            "\n" +
            "  attribute c: Access_Point = signal.a;\n" +
            "  attribute b: Access_Point = signal.b;\n" +
            "\n" +
            "  attribute c_after: Access_Point = new Access_Point(\n" +
            "    c.sect,\n" +
            "    c.co,\n" +
            "    true,\n" +
            "    c.isGreen\n" +
            "  );\n" +
            "\n" +
            "  attribute b_after: Access_Point = new Access_Point(\n" +
            "    b.sect,\n" +
            "    b.co,\n" +
            "    true,\n" +
            "    b.isGreen\n" +
            "  );\n" +
            "\n" +
            "  attribute co_c_after: Access_Point = new Access_Point(\n" +
            "    c.co.sect,\n" +
            "    c_after,\n" +
            "    false,\n" +
            "    c.co.isGreen\n" +
            "  );\n" +
            "\n" +
            "  attribute co_b_after: Access_Point = new Access_Point(\n" +
            "    b.co.sect,\n" +
            "    b_after,\n" +
            "    false,\n" +
            "    b.co.isGreen\n" +
            "  );\n" +
            "\n" +
            "  attribute untouched: Access_Point[*] = railway.access_points->select {\n" +
            "    in a: Access_Point;\n" +
            "    a != c & a != b & a != c.co & a != b.co\n" +
            "  };\n" +
            "\n" +
            "  attribute openedRailway: Railway_Network = new Railway_Network(\n" +
            "    access_points = untouched + (c_after, b_after, co_c_after, co_b_after),\n" +
            "    trains = railway.trains\n" +
            "  );\n" +
            "\n" +
            "  if Possible_Switch(c, b) ? openedRailway else railway\n" +
            "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    var focusTool = new FocusTool();
    focusTool.init();

    var gs = SysMLv2Mill.globalScope();

    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();
    var train = (OOTypeSymbol) gs.resolveType("Train").get();
    var railwayNetwork = (OOTypeSymbol) gs.resolveType("Railway_Network").get();
    var openUp = (OOTypeSymbol) gs.resolveType("OpenUp").get();

    var accessPointStruct = buildStruct(accessPoint, new TypePrinter());
    var trainStruct = buildStruct(train, new TypePrinter());
    var railwayNetworkStruct = buildStruct(railwayNetwork, new TypePrinter());
    var openUpStruct = buildStruct(openUp, new TypePrinter());

    focusTool.createSymbolTable(accessPointStruct);
    focusTool.completeSymbolTable(accessPointStruct);

    focusTool.createSymbolTable(trainStruct);
    focusTool.completeSymbolTable(trainStruct);

    focusTool.createSymbolTable(railwayNetworkStruct);
    focusTool.completeSymbolTable(railwayNetworkStruct);

    focusTool.createSymbolTable(openUpStruct);
    focusTool.completeSymbolTable(openUpStruct);

    SysMLTypeCheck3.init();
    List<String> focusModels = new ArrayList<>();

    var visitor = new SysMLActionsVisitor2() {
      @Override
      public void visit(ASTCalcDef node) {
        if (node.getName().equals("Phys_Trans_Open")) {
          focusModels.add(CalcDefTransformer.transform(node));
        }
      }
    };

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLActions(visitor);
    ast.accept(traverser);

    assertThat(focusModels).hasSize(1);

    assertThat(focusModels.get(0)).isEqualTo(
        "fun Phys_Trans_Open(railway: Railway_Network, signal: OpenUp) Railway_Network ="
            + " \"let var_c = (OpenUp_get_a signal); "
            + "var_b = (OpenUp_get_b signal); "
            + "var_c_after = (Access_PointConstr "
            + "(Access_Point_get_sect var_c) "
            + "(Access_Point_get_co var_c) "
            + "True "
            + "(Access_Point_get_isGreen var_c)); "
            + "var_b_after = (Access_PointConstr "
            + "(Access_Point_get_sect var_b) "
            + "(Access_Point_get_co var_b) "
            + "True "
            + "(Access_Point_get_isGreen var_b)); "
            + "var_co_c_after = (Access_PointConstr "
            + "(Access_Point_get_sect (Access_Point_get_co var_c)) "
            + "var_c_after "
            + "False "
            + "(Access_Point_get_isGreen (Access_Point_get_co var_c))); "
            + "var_co_b_after = (Access_PointConstr "
            + "(Access_Point_get_sect (Access_Point_get_co var_b)) "
            + "var_b_after "
            + "False "
            + "(Access_Point_get_isGreen (Access_Point_get_co var_b))); "
            + "var_untouched = filter (\\<lambda> a. "
            + "((((a \\<noteq> var_c) \\<and> (a \\<noteq> var_b)) "
            + "\\<and> (a \\<noteq> (Access_Point_get_co var_c))) "
            + "\\<and> (a \\<noteq> (Access_Point_get_co var_b)))) "
            + "(Railway_Network_get_access_points railway); "
            + "var_openedRailway = (Railway_NetworkConstr "
            + "(var_untouched + (var_c_after,var_b_after,var_co_c_after,var_co_b_after)) "
            + "(Railway_Network_get_trains railway)) "
            + "in (if (Possible_Switch var_c var_b) then var_openedRailway else railway)\"");
  }
}
