import {
  AstNode,
  CstNode,
  GrammarUtils,
  isAstNode,
  type ValidationAcceptor,
  type ValidationChecks,
} from "langium";
import type { DiagnosticRelatedInformation } from "vscode-languageserver";
import {
  isDeclFun,
  isRecord,
  PatternCons,
  type Binding,
  type DeclFun,
  type Extension,
  type LabelledPattern,
  type PatternRecord,
  type Program,
  type Record,
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
import { levenshtein } from "../utils.js";

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
    Record: validator.checkDuplicateRecordFields,
    PatternRecord: validator.checkDuplicateRecordFields,
    //TypeAsc: validator.checkTypeAscriptionsEnabled,
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
    const usedNames = new Map<string, DeclFun>();

    for (const decl of program.decls) {
      if (isDeclFun(decl)) {
        if (usedNames.has(decl.name)) {
          const previousDecl = usedNames.get(decl.name);

          accept("error", `Function '${decl.name}' is already defined`, {
            node: decl,
            property: "name",
            relatedInformation:
              this.getPreviousDefinitionRelatedInfo(previousDecl),
          });
        } else {
          usedNames.set(decl.name, decl);
        }
      }
    }
  }

  /**
   * Validates that the extensions used in a program are unique.
   */
  checkUniqueExtensions(program: Program, accept: ValidationAcceptor): void {
    const usedExtensions = new Map<string, CstNode | undefined>();

    for (const extension of program.extensions) {
      for (let i = 0; i < extension.extensionNames.length; i++) {
        const extensionName = extension.extensionNames[i];
        extension.$cstNode?.range;

        if (usedExtensions.has(extensionName)) {
          const previousExtension = usedExtensions.get(extensionName);

          accept("warning", `Extension '${extensionName}' is already in use`, {
            node: extension,
            property: "extensionNames",
            index: i,
            relatedInformation: this.getPreviousDefinitionRelatedInfo(
              previousExtension,
              "Originally included here"
            ),
            code: DiagnosticCodes.DUPLICATE_EXTENSION,
          });
        } else {
          const node = GrammarUtils.findNodeForProperty(
            extension.$cstNode,
            "extensionNames",
            i
          );
          usedExtensions.set(extensionName, node);
        }
      }
    }
  }

  /** Suggest the closest recognized extension name using Levenshtein distance */
  private suggestClosestExtensions(name: string): string[] {
    const candidates = [...extensionValues]
      .map((candidate) => ({
        candidate,
        distance: levenshtein(name, candidate),
      }))
      .filter(({ distance }) => distance <= 3)
      .sort((a, b) => a.distance - b.distance)
      .slice(0, 3)
      .map((a) => a.candidate);

    return candidates;
  }

  /**
   * Validates that the extensions used are recognized.
   */
  checkValidExtension(extension: Extension, accept: ValidationAcceptor): void {
    extension.extensionNames.forEach((extensionName, i) => {
      if (!extensionValues.has(extensionName)) {
        const suggestions = this.suggestClosestExtensions(extensionName);
        let message = `Unrecognized extension: ${extensionName}`;
        if (suggestions.length > 0) {
          message += ` (did you mean '${suggestions[0]}'?)`;
        }

        accept("error", message, {
          node: extension,
          property: "extensionNames",
          index: i,
          code: DiagnosticCodes.UNRECOGNIZED_EXTENSION,
          data: { suggestions },
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

  checkDuplicateRecordFields(
    record: Record | PatternRecord,
    accept: ValidationAcceptor
  ): void {
    const groups: Partial<
      globalThis.Record<string, Array<Binding | LabelledPattern>>
    > = isRecord(record)
      ? Object.groupBy(record.bindings, (binding) => binding.name)
      : Object.groupBy(record.patterns, (binding) => binding.label);

    Object.values(groups).forEach((bindings) => {
      bindings?.slice(1).forEach((binding) => {
        accept("error", "Duplicate field", {
          node: binding,
          relatedInformation: this.getPreviousDefinitionRelatedInfo(
            bindings[0]
          ),
        });
      });
    });
  }

  getPreviousDefinitionRelatedInfo(
    node: AstNode | CstNode | undefined,
    message = "Previously defined here"
  ): DiagnosticRelatedInformation[] {
    if (isAstNode(node)) {
      node = node.$cstNode;
    }

    const uri = node?.root?.astNode.$document?.textDocument.uri;
    const range = node?.range;

    if (!uri || !range) return [];

    return [
      {
        message,
        location: { uri, range },
      },
    ];
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
