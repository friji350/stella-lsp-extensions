import { EmptyFileSystem, type LangiumDocument } from "langium";
import { clearDocuments, parseHelper } from "langium/test";
import type { Diagnostic } from "vscode-languageserver-types";

import { createStellaServices } from "../../src/language/stella-module.js";
import { Program, isProgram } from "../../src/language/generated/ast.js";

export interface StellaAnalysis {
  document: LangiumDocument<Program>;
  parserErrors: string[];
  structuralErrors: string[];
  diagnostics: Diagnostic[];
  errorDiagnostics: Diagnostic[];
  errorTags: string[];
  hasErrors: boolean;
  allMessages: string[];
}

export class StellaTestHarness {
  private readonly services = createStellaServices(EmptyFileSystem);
  private readonly doParse = parseHelper<Program>(this.services.Stella);
  private currentDocument: LangiumDocument<Program> | undefined;

  async parse(input: string): Promise<StellaAnalysis> {
    await this.clear();
    const document = await this.doParse(input, { validation: true });
    this.currentDocument = document;
    return analyzeDocument(document);
  }

  async clear(): Promise<void> {
    if (this.currentDocument) {
      clearDocuments(this.services.shared, [this.currentDocument]);
      this.currentDocument = undefined;
    }
  }
}

export function analyzeDocument(
  document: LangiumDocument<Program>
): StellaAnalysis {
  const parserErrors = document.parseResult.parserErrors.map(
    (error) => error.message
  );
  const structuralErrors: string[] = [];

  if (document.parseResult.value === undefined) {
    structuralErrors.push("ParseResult is undefined.");
  } else if (!isProgram(document.parseResult.value)) {
    structuralErrors.push(
      `Root AST object is a ${document.parseResult.value.$type}, expected '${Program.$type}'.`
    );
  }

  const diagnostics = [...(document.diagnostics ?? [])];
  const errorDiagnostics = diagnostics.filter(
    (diagnostic) => diagnostic.severity === undefined || diagnostic.severity === 1
  );
  const errorTags = extractErrorTags(errorDiagnostics);
  const hasErrors =
    parserErrors.length > 0 ||
    structuralErrors.length > 0 ||
    errorDiagnostics.length > 0;

  return {
    document,
    parserErrors,
    structuralErrors,
    diagnostics,
    errorDiagnostics,
    errorTags,
    hasErrors,
    allMessages: [
      ...parserErrors,
      ...structuralErrors,
      ...diagnostics.map((diagnostic) => diagnostic.message),
    ],
  };
}

export function extractErrorTags(diagnostics: Diagnostic[]): string[] {
  const tags = new Set<string>();

  for (const diagnostic of diagnostics) {
    if (typeof diagnostic.code === "string" && diagnostic.code.startsWith("ERROR_")) {
      tags.add(diagnostic.code);
    }

    for (const match of diagnostic.message.matchAll(/\bERROR_[A-Z_]+\b/g)) {
      tags.add(match[0]);
    }
  }

  return [...tags].sort();
}
