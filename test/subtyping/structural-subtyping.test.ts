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

describe("Structural subtyping", () => {
  test("supports record width subtyping", async () => {
    document = await parse(`
      language core;

      extend with #records, #structural-subtyping, #nullary-functions;

      fn f(r : {x : Nat}) -> Nat {
        return r.x
      }

      fn main(n : Nat) -> Nat {
        return f({x = n, y = n})
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("supports variant subtyping", async () => {
    document = await parse(`
      language core;

      extend with #variants, #panic, #structural-subtyping, #structural-patterns, #unit-type;

      fn inc(r : <| value : Nat, failure : Unit |>) -> Nat {
        return match r {
          <| value = n |> => succ(n)
        | <| failure = _ |> => panic!
        }
      }

      fn just(n : Nat) -> <| value : Nat |> {
        return <| value = n |>
      }

      fn main(n : Nat) -> Nat {
        return inc(just(n))
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("supports function subtyping", async () => {
    document = await parse(`
      language core;

      extend with #records, #structural-subtyping, #nullary-functions;

      fn make() -> fn({x : Nat, y : Nat}) -> Nat {
        return fn(r : {x : Nat}) {
          return r.x
        }
      }

      fn main(n : Nat) -> Nat {
        return make()({x = n, y = n})
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("supports pair subtyping", async () => {
    document = await parse(`
      language core;

      extend with #pairs, #top-type, #structural-subtyping;

      fn fst(p : {Nat, Top}) -> Nat {
        return p.1
      }

      fn main(n : Nat) -> Nat {
        return fst({n, n})
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("supports list subtyping", async () => {
    document = await parse(`
      language core;

      extend with #lists, #top-type, #structural-subtyping;

      fn accept(xs : [Top]) -> Nat {
        return 0
      }

      fn main(n : Nat) -> Nat {
        return accept([n])
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("supports sum-type subtyping", async () => {
    document = await parse(`
      language core;

      extend with #sum-types, #top-type, #structural-subtyping, #type-ascriptions;

      fn accept(x : Nat + Top) -> Nat {
        return 0
      }

      fn main(n : Nat) -> Nat {
        return accept(inl(n) as Nat + Nat)
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("uses subtyping for declared exception types", async () => {
    document = await parse(`
      language core;

      extend with #exceptions, #exception-type-declaration, #top-type, #structural-subtyping;

      exception type = Top

      fn main(n : Nat) -> Nat {
        return throw(n)
      }
    `);

    expect(formatIssues(document)).toHaveLength(0);
  });

  test("keeps references invariant", async () => {
    document = await parse(`
      language core;

      extend with #references, #top-type, #structural-subtyping;

      fn main(n : Nat) -> &Top {
        return new(n)
      }
    `);

    expect(formatIssues(document)).toContain("not assignable");
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
