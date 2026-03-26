import { afterEach, beforeAll, describe, expect, test } from "vitest";
import { EmptyFileSystem, type LangiumDocument } from "langium";
import { clearDocuments, parseHelper } from "langium/test";
import { createStellaServices } from "../../src/language/stella-module.js";
import { Program, isProgram } from "../../src/language/generated/ast.js";

let services: ReturnType<typeof createStellaServices>;
let parse: ReturnType<typeof parseHelper<Program>>;
let document: LangiumDocument<Program> | undefined;

beforeAll(async () => {
  services = createStellaServices(EmptyFileSystem);
  const doParse = parseHelper<Program>(services.Stella);
  parse = (input: string) => doParse(input, { validation: true });
});

afterEach(async () => {
  if (document) {
    clearDocuments(services.shared, [document]);
    document = undefined;
  }
});

describe("Panic typing", () => {
  test("can be returned from a function with any declared return type", async () => {
    document = await parse(`
      language core;

      extend with #panic;

      fn main(n : Nat) -> Nat {
        return panic!
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("can type-check as both branches of an if-expression", async () => {
    document = await parse(`
      language core;

      extend with #panic;

      fn main(n : Nat) -> Nat {
        return if true then panic! else panic!
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });
});

function formatIssues(document: LangiumDocument<Program>): string {
  const structuralError = checkDocumentValid(document);
  if (structuralError) {
    return structuralError;
  }

  return (document.diagnostics ?? [])
    .map((diagnostic) => diagnostic.message)
    .join("\n");
}

function checkDocumentValid(
  document: LangiumDocument<Program>
): string | undefined {
  return (
    (document.parseResult.parserErrors.length > 0 &&
      `Parser errors:\n${document.parseResult.parserErrors
        .map((error) => error.message)
        .join("\n")}`) ||
    (document.parseResult.value === undefined && "ParseResult is undefined.") ||
    (!isProgram(document.parseResult.value) &&
      `Root AST object is a ${document.parseResult.value.$type}, expected '${Program.$type}'.`) ||
    undefined
  );
}
