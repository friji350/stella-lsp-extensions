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

describe("Exception typing", () => {
  test("allows throwing values of the declared exception type", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration, #structural-patterns;

      exception type = Nat

      fn main(n : Nat) -> Bool {
        return throw(succ(0))
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("type-checks try-with", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration, #structural-patterns;

      exception type = Nat

      fn fail(n : Nat) -> Bool {
        return throw(succ(0))
      }

      fn main(n : Nat) -> Bool {
        return try { fail(n) } with { false }
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("type-checks try-catch with a literal pattern", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration, #structural-patterns;

      exception type = Nat

      fn fail(n : Nat) -> Bool {
        return throw(succ(0))
      }

      fn main(n : Nat) -> Bool {
        return try { fail(n) } catch { 0 => true }
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("binds catch pattern variables to the declared exception type", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration;

      exception type = Nat

      fn fail(n : Nat) -> Bool {
        return throw(succ(0))
      }

      fn main(n : Nat) -> Bool {
        return try { fail(n) } catch { e => Nat::iszero(e) }
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("rejects thrown expressions of the wrong type", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration;

      exception type = Nat

      fn main(n : Nat) -> Bool {
        return throw(true)
      }
    `);

    expect(formatIssues(document)).toContain(
      "Thrown expressions must have the declared exception type Nat"
    );
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
