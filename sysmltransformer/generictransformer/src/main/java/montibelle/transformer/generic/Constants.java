package montibelle.transformer.generic;

import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.check.SymTypeOfObject;
import de.monticore.types.check.SymTypeOfTuple;
import de.monticore.types.check.SymTypePrimitive;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.TheorySymbol;
import montibelle.focus.symboltable.EnumType2TypeSymbolAdapter;
import montibelle.transformer.util.CountabilityVisitor;
import montibelle.transformer.util.FinitenessVisitor;

import java.util.List;
import java.util.Map;
import java.util.Optional;

public final class Constants {

  private Constants(){
  }

  public static final Constants instance = new Constants();

  public static char SEP = '_';

  public static final String SPS_PRFX = "sps";

  public static final String BNDL_PRFX = "bundle";

  public static final String REF_PRFX = "ref";

  public static final String REQ_PRFX = "req";

  public static final String CODE_PRFX = "code";

  public static final String CALC_PRFX = "calc";

  public static final Map<String, List<String>> FINITE_TYPES = Map.of(
      "bool", List.of("True", "False"),
      "bool \\<times> bool", List.of("(True, True)", "(True, False)", "(False, True)", "(False, False)")
  );

  public static boolean isTypeCountable(SymTypeExpression expression) {
    CountabilityVisitor visitor = new CountabilityVisitor();
    if(expression == null) return false;
    return visitor.calculate(expression);
  }

  public static boolean isTypeFinite(SymTypeExpression expression) {
    FinitenessVisitor visitor = new FinitenessVisitor();
    if(expression == null) return false;
    return visitor.calculate(expression);
  }

  public static List<String> getFiniteChoices(SymTypeExpression expression) {
    if(!isTypeFinite(expression))
      return List.of();
    if(expression instanceof SymTypePrimitive) {
      var primitive = ((SymTypePrimitive) expression).getPrimitiveName();
      if(primitive.equals("boolean")) {
        return List.of("True", "False");
      }
    }
    if(expression instanceof SymTypeOfTuple) {
      var tuple = ((SymTypeOfTuple) expression).printFullName();
      if(tuple.equals("(boolean, boolean)")) {
        return List.of("(True, True)", "(True, False)", "(False, True)",
            "(False, False)");
      }
    }
    if(expression instanceof SymTypeOfObject) {
      var object = (SymTypeOfObject) expression;
      if(!object.hasTypeInfo()) {
        return List.of();
      }
      if(object.getTypeInfo() instanceof EnumType2TypeSymbolAdapter) {
        return ((EnumType2TypeSymbolAdapter) object.getTypeInfo()).getFiniteChoicesList();
      }
    }
    return List.of();
  }

  public static Optional<TheorySymbol> getTheoryFor(
      SymTypeExpression type
  ) {
    String theoryName = type.printFullName();

    return FocusMill.globalScope()
        .resolveTheory("user." + theoryName);
  }

  public static final String theories = "theories";
  public static final String sessions = "sessions";
  public static final String scala = "scala";

  public static final String TSYNAUT_REF = theories + "/refinement/TimesliceAutomata.ftl";

  public static final String REQUIREMENT_TEMPLATE = theories + "/Requirement.ftl";
  public static final String REQUIREMENT_EXECUTABLE_TEMPLATE =
      theories + "/RequirementExec.ftl";
  public static final String FUN_DEF = theories + "/Function.ftl";
  public static final String BUNDLE_DEF = theories + "/Bundle.ftl";
  public static final String COMPOSITION = theories + "/Composition.ftl";
  public static final String CONNECTOR = theories + "/Connector.ftl";
  public static final String DATA_INC = theories + "/Data_inc.ftl";
  public static final String DATATYPES = theories + "/Datatypes.ftl";
  public static final String ENUM = theories + "/Enum.ftl";
  public static final String STRUCT = theories + "/Struct.ftl";
  public static final String INSTANCE = theories + "/Instance.ftl";
  public static final String SPEC = theories + "/Specification.ftl";
  public static final String STATES = theories + "/States.ftl";
  public static final String TSYN_AUT = theories + "/TsynAutomaton.ftl";
  public static final String EVENT_AUTOMATON = theories + "/EventAutomaton.ftl";

  public static final String EVENTAUT_REF = theories + "/refinement/EventAutomata.ftl";
  public static final String AUTOMATIC_HLR_NARROWING = theories + "/refinement/AutomaticHlrNarrowing.ftl";
  public static final String HLR_DECOMPOSITION = theories + "/refinement/HlrDecomposition.ftl";
  public static final String GENERAL_REF = theories + "/refinement/Refinement.ftl";
  public static final String COMPOSITE_HLR_NARROWING = theories + "/refinement/CompositeHlrNarrowing.ftl";
  public static final String EVENT_LLR2HLR = theories + "/refinement/LlrRefinementEvent.ftl";

  public static final String INCR_CODE_BUNDLE_TEMPLATE = theories + "/code/CodeBundle.ftl";
  public static final String INCR_CODE_EVENTAUT_TEMPLATE = theories + "/code/CodeEventAutomaton.ftl";
  public static final String INCR_CODE_TSYNAUT_TEMPLATE = theories + "/code/CodeTsynAutomaton.ftl";

  public static final String INCR_SIMULATOR_TEMPLATE = "scala/EventAutomatonSimulator.ftl";

  public static final String ROOT_TEMPLATE = sessions + "/ROOT.ftl";
  public static final String ROOTS_TEMPLATE = sessions + "/ROOTS.ftl";

  public static final String ISABELLE_NULL = "\\<sim>";
  public static final String ISABELLE_TRUE = "True";

}
