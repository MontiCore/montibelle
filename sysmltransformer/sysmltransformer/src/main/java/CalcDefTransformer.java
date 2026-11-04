import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.lang.sysmlactions._ast.ASTCalcDef;
import de.monticore.lang.sysmlbasis._ast.ASTSysMLTyping;
import de.monticore.lang.sysmlparts._ast.ASTAttributeUsage;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2._ast.ASTAnonymousUsage;
import java.util.ArrayList;
import java.util.List;
import static montibelle.transformer.sysml.Main.getEventExpressionPrinter;

public class CalcDefTransformer {

  public static String transform(ASTCalcDef node) {
    List<String> param = new ArrayList<>();
    List<String> localLets = new ArrayList<>();
    String returnType = "";

    for (Object elem : node.getSysMLElementList()) {
      if (elem instanceof ASTAnonymousUsage) {
        ASTAnonymousUsage usage = (ASTAnonymousUsage) elem;
        String type = extractType(usage);

        if (usage.isPresentName()) {
          param.add(usage.getName() + ": " + type);
        } else {
          returnType = type;
        }
      }

      else if (elem instanceof ASTAttributeUsage) {
        ASTAttributeUsage usage = (ASTAttributeUsage) elem;

        if (usage.isPresentName() && usage.isPresentDefaultValue()) {
          var traverser = SysMLv2Mill.inheritanceTraverser();
          var printer = getEventExpressionPrinter(traverser);

          ASTExpression value =
              usage.getDefaultValue().getExpression();

          localLets.add("var_" + usage.getName() + " = " + printer.print(value));
        }
      }
    }

    String expression = "";
    if (node.isPresentExpression()) {
      var traverser = SysMLv2Mill.inheritanceTraverser();
      var printer = getEventExpressionPrinter(traverser);
      expression = printer.print(node.getExpression());
    }

    if (!localLets.isEmpty()) {
      expression = "let " + String.join("; ", localLets) + " in " + expression;
    }

    return "fun " + node.getName()
        + "(" + String.join(", ", param) + ") "
        + returnType
        + " = \"" + expression + "\"";
  }

  private static String extractType(ASTAnonymousUsage usage) {
    if (!usage.getSpecializationList().isEmpty()) {
      Object spec = usage.getSpecializationList().get(0);
      if (spec instanceof ASTSysMLTyping) {
        ASTSysMLTyping typing = (ASTSysMLTyping) spec;

        String type = "";
        if (!typing.getSuperTypesList().isEmpty()) {
          type = SysMLv2Mill.prettyPrint(typing.getSuperTypesList().get(0), false).trim();
        }

        if (typing.isPresentCardinality()) {
          type += " set";
        }

        return type;
      }
    }
    return "";
  }
}

