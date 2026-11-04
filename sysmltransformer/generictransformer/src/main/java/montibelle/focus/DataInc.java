package montibelle.focus;

import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol;
import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbol;
import kotlin.Pair;
import montibelle.focus._ast.ASTDataInc;
import montibelle.focus._ast.ASTDatatypesBuilder;
import montibelle.focus._ast.ASTFocusFunction;
import montibelle.focus._ast.ASTEnumType;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.focus._ast.ASTUserDefinedStruct;
import montibelle.focus._symboltable.ChannelTypeSymbol;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.generic.sessions.SessionGenerator;
import montibelle.transformer.util.FreemarkerInterface;
import trafos.ITypePrinter;

import java.io.IOException;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static cc2focus.OOTypeSymbol2FocusType.buildEnum;
import static cc2focus.OOTypeSymbol2FocusType.buildStruct;

public final class DataInc {

  private DataInc() {
  }

  public static Pair<ASTTheory, ASTSession> createTheoryFrom(ASTDataInc node) {
    ASTSession session = new ASTSessionBuilder()
        .setName("data_inc")
        .setPathList(List.of("inc"))
        .build();

    session.setParent("bundlelocale");
    session.addGroup("system");

    ASTTheory theory = new ASTTheoryBuilder()
        .setSessionName(session.getName())
        .setFilename("Data_inc")
        .build();

    node.setTheory(theory.getName());

    return new Pair<>(theory, session);
  }

  public static void generateUserDataInc(
      java.nio.file.Path target,
      List<TypeSymbol> userDefinedTypes,
      List<ChannelTypeSymbol> chanTypes,
      List<String> calcDefs,
      ITypePrinter typePrinter,
      SessionGenerator sessionGenerator,
      boolean comment
  ) {
    FocusTool focusTool = new FocusTool();
    var gs = FocusMill.globalScope();

    List<ASTEnumType> newEnums = userDefinedTypes.stream()
        .map(it -> (OOTypeSymbol) it)
        .collect(Collectors.toList()).stream()
        .filter(OOTypeSymbol::isIsEnum)
        .map(it -> buildEnum(it))
        .collect(Collectors.toList());

    List<ASTUserDefinedStruct> newStructs = userDefinedTypes.stream()
        .map(it -> (OOTypeSymbol) it)
        .collect(Collectors.toList()).stream()
        .filter(it -> !it.isIsEnum())
        .map(it -> buildStruct(it, typePrinter))
        .collect(Collectors.toList());

    newEnums.forEach(it -> {
      var existing = gs.resolveEnumType(it.getName());
      if (existing.isPresent()) {
        var scope = existing.get().getEnclosingScope();
        scope.remove(existing.get());
        scope.getEnclosingScope().removeSubScope(scope);
      }
    });

    newStructs.forEach(it -> {
      var existing = gs.resolveUserDefinedStruct(it.getName());
      if (existing.isPresent()) {
        var scope = existing.get().getEnclosingScope();
        scope.remove(existing.get());
        scope.getEnclosingScope().removeSubScope(scope);
      }
    });

    newEnums.forEach(it -> focusTool.createSymbolTable(it));
    newStructs.forEach(it -> focusTool.createSymbolTable(it));

    newEnums.forEach(it -> focusTool.completeSymbolTable(it));
    newStructs.forEach(it -> focusTool.completeSymbolTable(it));

    var oldDatatypes = gs.resolveDatatypes("Datatypes");

    List<String> oldChanTypes = oldDatatypes.isPresent() ? oldDatatypes.get().getChannelTypesList() : List.of();
    final List<String> finalOldChanTypes1 = oldChanTypes;
    List<String> newChanTypes = chanTypes.stream().map(ChannelTypeSymbol::getName)
        .filter(n -> !finalOldChanTypes1.contains(n)).collect(Collectors.toList());
    List<String> allChanTypes = new java.util.ArrayList<>(oldChanTypes);
    allChanTypes.addAll(newChanTypes);
    allChanTypes = allChanTypes.stream().distinct().sorted().collect(Collectors.toList());

    List<String> newEnumNames = newEnums.stream()
        .map(ASTEnumType::getName)
        .collect(Collectors.toList());

    List<String> oldEnums = oldDatatypes.isPresent()
        ? oldDatatypes.get().getUserDefinedEnumsList().stream()
        .filter(name -> !newEnumNames.contains(name))
        .collect(Collectors.toList())
        : List.of();

    List<String> allEnums = Stream.concat(
            oldEnums.stream(), newEnumNames.stream())
        .distinct()
        .collect(Collectors.toList());

    List<String> newStructNames = newStructs.stream()
        .map(ASTUserDefinedStruct::getName)
        .collect(Collectors.toList());

    List<String> oldStructs = oldDatatypes.isPresent()
        ? oldDatatypes.get().getUserDefinedStructsList().stream()
        .filter(name -> !newStructNames.contains(name))
        .collect(Collectors.toList())
        : List.of();

    List<String> allStructs = Stream.concat(
            oldStructs.stream(), newStructNames.stream())
        .distinct()
        .collect(Collectors.toList());

    if (oldDatatypes.isPresent()) {
      gs.removeSubScope(oldDatatypes.get().getTheorySymbol().getSession().getEnclosingScope());
      gs.removeSubScope(oldDatatypes.get().getTheorySymbol().getEnclosingScope());
      gs.removeSubScope(oldDatatypes.get().getEnclosingScope());
    }

    List<ASTFocusFunction> newFunctions = calcDefs.stream()
      .map(c -> {
        try {
          return FocusMill.parser().parse_StringFocusFunction(c).get();
        } catch (IOException e) {
          throw new RuntimeException(e);
        }
      })
      .collect(Collectors.toList());

    for(var function: newFunctions) {
      focusTool.createSymbolTable(function);
      focusTool.completeSymbolTable(function);
    }

    List<String> oldFunctions = oldDatatypes.isPresent()
        ? oldDatatypes.get().getFunctionsList()
        : List.of();

    List<String> allFunctions = Stream.concat(
            oldFunctions.stream(),
            newFunctions.stream().map(
                fn -> Constants.CALC_PRFX + Constants.SEP + fn.getName()
            )
        )
        .distinct()
        .collect(Collectors.toList());

    var datatypes = new ASTDatatypesBuilder()
        .setChannelTypesList(allChanTypes)
        .setUserDefinedStructsList(allStructs)
        .setUserDefinedEnumsList(allEnums)
        .setFocusFunctionsList(allFunctions)
        .uncheckedBuild();
    focusTool.createSymbolTable(datatypes);

    var datatypesPair = Datatypes.createTheoryFrom(datatypes);
    var datatypesTheory = datatypesPair.getFirst();
    var datatypesSession = datatypesPair.getSecond();
    focusTool.createSymbolTable(datatypesTheory);
    focusTool.createSymbolTable(datatypesSession);

    for (ASTEnumType _enum : newEnums) {
      var enumThy = Datatypes.createTheoryFrom(
          _enum.getName(),
          datatypesTheory
      );

      focusTool.createSymbolTable(enumThy);
      focusTool.completeSymbolTable(enumThy);

      if (enumThy.isSubstituted()) {
        continue;
      }

      FreemarkerInterface.instance.generate(
          Constants.ENUM,
          target.resolve(datatypesSession.getPath().resolve(
              enumThy.getFilename() + ".thy")
          ).toAbsolutePath(),
          comment,
          enumThy,
          _enum
      );

      sessionGenerator.add(enumThy);
    }

    for (ASTFocusFunction function : newFunctions) {
      var funTheory = Datatypes.createTheoryFrom(
          Constants.CALC_PRFX + Constants.SEP + function.getName(),
          datatypesTheory
      );

      focusTool.createSymbolTable(funTheory);
      focusTool.completeSymbolTable(funTheory);

      if (funTheory.isSubstituted()) {
        continue;
      }

      FreemarkerInterface.instance.generate(
        Constants.FUN_DEF,
        target.resolve(datatypesSession.getPath().resolve(
            funTheory.getFilename() + ".thy")
        ).toAbsolutePath(),
        comment,
        funTheory,
        function,
        Constants.instance
      );

      sessionGenerator.add(funTheory);
    }

    for (String oldFun : oldFunctions) {
      var funTheory = Datatypes.createTheoryFrom(oldFun, datatypesTheory);
      if (funTheory.isSubstituted()) {
        continue;
      }

      sessionGenerator.add(funTheory);
    }

    for (var oldEnum : oldEnums) {
      var funTheory = Datatypes.createTheoryFrom(oldEnum, datatypesTheory);
      if (funTheory.isSubstituted()) {
        continue;
      }

      sessionGenerator.add(funTheory);
    }

    focusTool.completeSymbolTable(datatypes);
    focusTool.completeSymbolTable(datatypesTheory);
    focusTool.completeSymbolTable(datatypesSession);

    if(!datatypesTheory.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.DATATYPES,
          target.resolve(datatypesSession.getPath().resolve(
              datatypesTheory.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          datatypesTheory,
          datatypes,
          Constants.instance
      );

      sessionGenerator.add(datatypesTheory);
    }

    var oldDataInc = gs.resolveDataInc("DataInc");

    if (oldDataInc.isPresent()) {
      gs.removeSubScope(oldDataInc.get().getTheorySymbol().getSession().getEnclosingScope());
      gs.removeSubScope(oldDataInc.get().getTheorySymbol().getEnclosingScope());
      gs.removeSubScope(oldDataInc.get().getEnclosingScope());
    }

    oldChanTypes = oldDataInc.isPresent() ? oldDataInc.get().getChannelTypesList() : List.of();
    final List<String> finalOldChanTypes2 = oldChanTypes;
    newChanTypes = chanTypes.stream().map(ChannelTypeSymbol::getName)
        .filter(n -> !finalOldChanTypes2.contains(n)).collect(Collectors.toList());
    allChanTypes = new java.util.ArrayList<>(oldChanTypes);
    allChanTypes.addAll(newChanTypes);
    allChanTypes = allChanTypes.stream().distinct().sorted().collect(Collectors.toList());

    var dataInc = new montibelle.focus._ast.ASTDataIncBuilder()
      .setChannelTypesList(allChanTypes)
      .uncheckedBuild();
    focusTool.createSymbolTable(dataInc);

    var pair = createTheoryFrom(dataInc);
    var t = pair.getFirst();
    var s = pair.getSecond();
    focusTool.createSymbolTable(t);
    focusTool.createSymbolTable(s);

    focusTool.completeSymbolTable(dataInc);
    focusTool.completeSymbolTable(t);
    focusTool.completeSymbolTable(s);

    if (!t.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.DATA_INC,
          target.resolve(s.getPath().resolve(t.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          t,
          dataInc
      );

      sessionGenerator.add(t);
    }
  }

}
