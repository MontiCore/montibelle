import de.monticore.generating.GeneratorEngine
import de.monticore.generating.GeneratorSetup
import de.monticore.io.paths.ModelPath
import de.monticore.symboltable.GlobalScope
import de.monticore.umlcd4a.CD4AnalysisLanguage
import de.monticore.umlcd4a.symboltable.CDMethodSymbol
import de.monticore.umlcd4a.symboltable.CDSymbol
import de.monticore.umlcd4a.symboltable.CDTypeSymbol
import org.apache.commons.io.FileUtils
import org.apache.commons.io.FilenameUtils

import java.nio.file.Path
import java.nio.file.Paths
import java.util.stream.Collectors

class Client {

  String name;
  List<Field> fields;
  boolean export;

  Client(String name, List<Field> fields, boolean export) {
    this.name = name;
    this.fields = fields;
    this.export = export;
  }

  Client(String name, List<Field> fields) {
    this(name, fields, false);
  }

  Client(String name) {
    this(name, new ArrayList<Field>(), false);
  }

  void addField(Field field) {
    this.fields.add(field);
  }

}

class Field {

  String name;
  String type;

  Field(String name, String type){
    this.name = name;
    this.type = type;
  }

}


Path basePath = Paths.get("src/main/rpc/")

GlobalScope globalScope = new GlobalScope(new ModelPath(basePath), new CD4AnalysisLanguage());

cdSymbols = []
basePath.toFile().traverse(nameFilter: ~/.*\.cd$/) {
  String fullyQualifiedName = FilenameUtils.removeExtension(basePath.relativize(it.toPath()).iterator().join("."));
  CDSymbol cdSymbol = globalScope.<CDSymbol>resolve(fullyQualifiedName, CDSymbol.KIND).orElse(null);

  if(cdSymbol == null) {
    throw new RuntimeException("Cannot find Symbol " + fullyQualifiedName + " for " + it.toString() + ".\n"
        + "ClassDiagrams names and packages must match the file structure.");
  }
  else {
    cdSymbols.add(cdSymbol);
  }
}

moreThenOneInterface = cdSymbols
    .stream()
    .filter(cdSymbol -> cdSymbol.getTypes().stream().filter(type -> type.isInterface()).count() > 1)
    .collect(Collectors.toList());

if(!moreThenOneInterface.isEmpty()){
  moreThenOneInterface.forEach(cdSymbol -> println(cdSymbol.getFullName() + " specified more then one interface."));
  throw new RuntimeException("Some interfaces specified more then one interface.");
}

differentlyNamedInterfaces = cdSymbols
    .stream()
    .flatMap(cdSymbol -> cdSymbol.getTypes().stream().filter(type -> type.isInterface() && !type.name.equals(cdSymbol.name)))
    .collect(Collectors.toList());

if(!differentlyNamedInterfaces.isEmpty()){
  differentlyNamedInterfaces.forEach(interface_ -> println(interface_.getFullName() + " didn't match the Class Diagrams name."));
  throw new RuntimeException("Some interface names didn't match the name of the defining Class Diagram.");
}

interfaceWithMultipleMethods = cdSymbols
    .stream()
    .flatMap(cdSymbol -> cdSymbol.getTypes().stream().filter(type -> type.isInterface()))
    .filter(interface_ -> {
      Set<CDMethodSymbol> temporarySet = new HashSet<>();
      return interface_.getMethods().stream().map(method -> method.name).anyMatch(method -> !temporarySet.add(method));
    })
    .collect(Collectors.toList());

if(!interfaceWithMultipleMethods.isEmpty()){
  interfaceWithMultipleMethods.forEach(interface_ -> println(interface_.getFullName() + " has multiple methods with same name."));
  throw new RuntimeException("Some interfaces had multiple methods with same name.");
}


def outputDir = new File("target/generated/")

GeneratorSetup setup = new GeneratorSetup();
setup.setOutputDirectory(outputDir);
setup.setCommentStart("/*-- ");
setup.setCommentEnd(" --*/");
setup.setAdditionalTemplatePaths([new File("src/generation/freemarker/templates")]);
setup.setTracing(true);
GeneratorEngine engine = new GeneratorEngine(setup);

List<CDTypeSymbol> customTypes = cdSymbols
    .stream()
    .flatMap(it -> it.getTypes().stream())
    .filter(it -> !it.getAllVisibleFields().isEmpty())
    .collect(Collectors.toList());

for(def cdSymbol : cdSymbols) {
  println("Transforming " + cdSymbol);

  for(def type : cdSymbol.getTypes().findAll{ !it.isAbstract() }) {
    def packPath = type.getPackageName().replace(".", "/");
    def fullPath = (packPath.isEmpty() ? "" : packPath + "/") + cdSymbol.getName().toLowerCase() + "/" + type.getName();

    engine.generateNoA("java/Type.java.ftl", Paths.get("java/" + fullPath + ".java"), (Object) type);
    engine.generateNoA("ts/Type.ts.ftl", Paths.get("ts/" + fullPath + ".ts"), (Object) type, (Object) customTypes);
  }

  for (def interface_ : cdSymbol.getTypes().findAll { it.isInterface() }) {
    def packPath = interface_.getPackageName().replace(".", "/");
    def fullPath = (packPath.isEmpty() ? "" : packPath + "/") + cdSymbol.getName().toLowerCase() + "/" + interface_.getName();

    engine.generateNoA("java/Interface.java.ftl", Paths.get("java/" + fullPath + ".java"), (Object) interface_);
    engine.generateNoA("ts/Interface.ts.ftl", Paths.get("ts/"  + fullPath + ".ts"), (Object) interface_, (Object) customTypes);
  }
}

List<CDTypeSymbol> interfaces = cdSymbols
    .stream()
    .flatMap(it -> it.getTypes().stream())
    .filter(it -> it.isInterface())
    .collect(Collectors.toList());

println("TypeScript: Generating BackboneClient.ts")

clients = new ArrayList<Client>();
Client backboneClient = new Client("BackboneClient", new ArrayList<Field>(), true);
clients.add(backboneClient)

for(def interface_ : interfaces) {

  String fieldTypePrefix = "";
  Client lastClient = backboneClient;

  for(def fieldName: interface_.getPackageName().split("\\.")) {

    def fieldType;
    if(fieldTypePrefix.equals("")) {
      fieldTypePrefix = fieldName;
      fieldType = fieldName.capitalize();
    }
    else {
      fieldTypePrefix += "_" + fieldName;
      fieldType = fieldTypePrefix + "_" + fieldName.capitalize();
    }

    if(lastClient.fields.stream().noneMatch(f -> f.name.equals(fieldName))) {
      lastClient.addField(new Field(fieldName, fieldType));
    }

    Optional<Client> optClient = clients.stream().filter(c -> c.name.equals(fieldType)).findFirst();
    if(!optClient.isPresent()) {
      optClient = Optional.of(new Client(fieldType))
      clients.add(optClient.get());
    }

    lastClient = optClient.get();
  }

  lastClient.addField(new Field(interface_.name, fieldTypePrefix + "_" + interface_.enclosingScope.name.get().toLowerCase() + "_" + interface_.name + "Client"));
}

engine.generateNoA("ts/BackboneClient.ts.ftl", Paths.get("ts/BackboneClient.ts"), (Object) interfaces, (Object) clients);

version = System.properties['version']

if(version.contains("SNAPSHOT")) {
  version += "." + (new Date()).getTime()
}

println("TypeScript: Generating package.json with version " + version)

setup.setTracing(false);
engine.generateNoA("ts/package.json.ftl", Paths.get("ts/package.json"), version);
setup.setTracing(true);

println("TypeScript: Copying static files")
FileUtils.copyDirectory(new File("src/generation/static"), outputDir)
