export namespace Validation {

  export function isValidFileName(fileName:string){
    var forbiddenChars = /\\|\/|:|\*|\?|"|<|>|\|/;
    var dontStartWith = /^\./;
    var forbiddenNames = /^(nul|prn|con|lpt[0-9]|com[0-9])(\.|$)/i;
    return !forbiddenChars.test(fileName) && !dontStartWith.test(fileName) && !forbiddenNames.test(fileName);
  }

  export function isValidComponentName(componentName:string){
    var pascalCase = /^[A-Z]+[a-zA-Z0-9]*$/;
    var forbiddenNames = /^(nul|prn|con|lpt[0-9]|com[0-9])(\.|$)/i;
    return pascalCase.test(componentName) && !forbiddenNames.test(componentName);
  }

  export function isValidPackageName(packageName:string){
    var camelCase = /^[a-z]+[a-zA-Z0-9]*$/;
    var forbiddenNames = /^(nul|prn|con|lpt[0-9]|com[0-9])(\.|$)/i;
    return camelCase.test(packageName) && !forbiddenNames.test(packageName);
  }
}
