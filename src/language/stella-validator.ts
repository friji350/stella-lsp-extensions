import {
  GrammarUtils,
  type ValidationAcceptor,
  type ValidationChecks,
} from "langium";
import type { Range } from "vscode-languageserver";
import {
  isDeclFun,
  PatternCons,
  type Extension,
  type Program,
  type StellaAstType,
  type TypeAsc,
} from "./generated/ast.js";
import type { StellaServices } from "./stella-module.js";
import {
  extensionValues,
  Extensions,
  getExtensions,
} from "./extensions.js";
import { DiagnosticCodes } from "./validator/errors.js";

/**
 * Register custom validation checks.
 */
export function registerValidationChecks(services: StellaServices) {
  const registry = services.validation.ValidationRegistry;
  const validator = services.validation.StellaValidator;
  const checks: ValidationChecks<StellaAstType> = {
    Program: [
      validator.checkUniqueExtensions,
      validator.checkHasMain,
      validator.checkUniqueFunctionNames,
    ],
    Extension: validator.checkValidExtension,
    PatternCons: validator.checkModernPatternConsSyntax,
    TypeAsc: validator.checkTypeAscriptionsEnabled,
  };
  registry.register(checks, validator);
}

/**
 * Implementation of custom validations.
 */
export class StellaValidator {
  checkHasMain(program: Program, accept: ValidationAcceptor): void {
    if (!program.decls.filter(isDeclFun).some((decl) => decl.name === "main")) {
      accept("error", "Missing main function", {
        node: program,
        property: "langDecl", // To not highlight the whole program
        code: DiagnosticCodes.MISSING_MAIN,
      });
    }
  }

  checkUniqueFunctionNames(program: Program, accept: ValidationAcceptor): void {
    const usedNames = new Map<string, Range | undefined>();

    for (const decl of program.decls) {
      if (isDeclFun(decl)) {
        if (usedNames.has(decl.name)) {
          const range = usedNames.get(decl.name);
          accept("error", `Function '${decl.name}' is already defined`, {
            node: decl,
            property: "name",
            relatedInformation: range
              ? [
                  {
                    location: {
                      uri: program.$document!.textDocument.uri,
                      range,
                    },
                    message: "Originally defined here",
                  },
                ]
              : [],
          });
        } else {
          usedNames.set(decl.name, decl.$cstNode?.range);
        }
      }
    }
  }

  /**
   * Validates that the extensions used in a program are unique.
   */
  checkUniqueExtensions(program: Program, accept: ValidationAcceptor): void {
    // TODO: make it a Map and store the location of the extension for use in "relatedInformation"
    const usedExtensions = new Map<string, Range | undefined>();

    for (const extension of program.extensions) {
      for (let i = 0; i < extension.extensionNames.length; i++) {
        const extensionName = extension.extensionNames[i];
        extension.$cstNode?.range;

        if (usedExtensions.has(extensionName)) {
          const range = usedExtensions.get(extensionName);

          accept("warning", `Extension '${extensionName}' is already in use`, {
            node: extension,
            property: "extensionNames",
            index: i,
            relatedInformation: range
              ? [
                  {
                    location: {
                      uri: program.$document!.textDocument.uri,
                      range,
                    },
                    message: "Originally included here",
                  },
                ]
              : [],
            code: DiagnosticCodes.DUPLICATE_EXTENSION,
          });
        } else {
          const node = GrammarUtils.findNodeForProperty(
            extension.$cstNode,
            "extensionNames",
            i
          );
          usedExtensions.set(extensionName, node?.range);
        }
      }
    }
  }

  /**
   * Validates that the extensions used are recognized.
   */
  checkValidExtension(extension: Extension, accept: ValidationAcceptor): void {
    extension.extensionNames.forEach((extensionName, i) => {
      if (!extensionValues.has(extensionName)) {
        // TODO: check for possible typos and suggest alternatives
        accept("error", `Unrecognized extension: ${extensionName}`, {
          node: extension,
          property: "extensionNames",
          index: i,
        });
      }
    });
  }

  checkModernPatternConsSyntax(
    patternCons: PatternCons,
    accept: ValidationAcceptor
  ): void {
    if (!patternCons.usesNewSyntax) {
      accept(
        "warning",
        "This syntax is deprecated. Please use 'cons' instead.",
        {
          node: patternCons,
          code: DiagnosticCodes.LEGACY_PATTERN_CONS,
        }
      );
    }
  }

  checkTypeAscriptionsEnabled(
    typeAsc: TypeAsc,
    accept: ValidationAcceptor
  ): void {
    const program = typeAsc.$document?.parseResult?.value as Program | undefined;
    if (!program) {
      return;
    }

    if (!getExtensions(program).has(Extensions.TypeAscriptions)) {
      accept(
        "error",
        "Type ascriptions require the '#type-ascriptions' extension",
        {
          node: typeAsc,
          code: DiagnosticCodes.TYPE_ASCRIPTIONS_EXTENSION_REQUIRED,
        }
      );
    }
  }

  // TODO: add all validations from https://github.com/fizruk/stella/blob/main/stella/src/Language/Stella/ExtensionCheck.hs
}
