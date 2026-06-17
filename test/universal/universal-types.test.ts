import { afterEach, describe, expect, test } from "vitest";

import { StellaTestHarness, type StellaAnalysis } from "../utils/stella-test-harness.js";

const harness = new StellaTestHarness();

afterEach(async () => {
  await harness.clear();
});

describe("Explicit universal types", () => {
  test("accepts a generic function with an explicit type application", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      generic fn identity[X](x : X) -> X {
        return x
      }

      fn main(n : Nat) -> Nat {
        return identity[Nat](n)
      }
    `);

    expectNoIssues(result);
  });

  test("accepts a returned universal function and instantiates it", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      generic fn const[X](x : X) -> forall Y. fn(Y) -> X {
        return generic [Y] fn(y : Y) { return x }
      }

      fn main(n : Nat) -> Nat {
        return const[Nat](n)[Bool](false)
      }
    `);

    expectNoIssues(result);
  });

  test("rejects too few type arguments", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      generic fn const[X, Y](x : X) -> fn(Y) -> X {
        return fn(y : Y) { return x }
      }

      fn main(n : Nat) -> Nat {
        return const[Nat](n)(false)
      }
    `);

    expectCleanSyntax(result);
    expect(result.errorTags).toContain("ERROR_INCORRECT_NUMBER_OF_TYPE_ARGUMENTS");
  });

  test("rejects type arguments on a non-generic function", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      fn const(x : Nat) -> forall Y. fn(Y) -> Nat {
        return generic [Y] fn(y : Y) { return x }
      }

      fn main(n : Nat) -> Nat {
        return const[Nat](n)[Bool](false)
      }
    `);

    expectCleanSyntax(result);
    expect(result.errorTags).toContain("ERROR_NOT_A_GENERIC_FUNCTION");
  });

  test("rejects duplicate type parameters", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      generic fn bad[X, X](x : X) -> X {
        return x
      }

      fn main(n : Nat) -> Nat {
        return bad[Nat, Nat](n)
      }
    `);

    expectCleanSyntax(result);
    expect(result.errorTags).toContain("ERROR_DUPLICATE_TYPE_PARAMETER");
  });

  test("rejects a universal function body with an incompatible quantified return type", async () => {
    const result = await harness.parse(`
      language core;

      extend with #universal-types;

      generic fn id[X](a : X) -> forall X. fn(X) -> X {
        return generic [X] fn(b : X) {
          return a
        }
      }

      fn main(n : Nat) -> Nat {
        return n
      }
    `);

    expectCleanSyntax(result);
    expect(result.errorTags).toContain("ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION");
  });
});

function expectNoIssues(result: StellaAnalysis): void {
  expect(result.allMessages.join("\n")).toBe("");
  expect(result.hasErrors).toBe(false);
}

function expectCleanSyntax(result: StellaAnalysis): void {
  expect([...result.parserErrors, ...result.structuralErrors]).toHaveLength(0);
}
