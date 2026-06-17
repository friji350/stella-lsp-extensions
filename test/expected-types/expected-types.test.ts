import { afterEach, describe, expect, test } from "vitest";

import { StellaTestHarness, type StellaAnalysis } from "../utils/stella-test-harness.js";

const harness = new StellaTestHarness();

afterEach(async () => {
  await harness.clear();
});

describe("Expected type propagation", () => {
  test("types an empty list from the declared return type", async () => {
    const result = await harness.parse(`
      language core;

      extend with #lists;

      fn main(n : Nat) -> [Nat] {
        return []
      }
    `);

    expectNoIssues(result);
  });

  test("types sum injections from the declared return type", async () => {
    const result = await harness.parse(`
      language core;

      extend with #sum-types, #unit-type;

      fn main(n : Nat) -> Nat + Unit {
        return inl(n)
      }
    `);

    expectNoIssues(result);
  });

  test("types variant labels from the declared return type", async () => {
    const result = await harness.parse(`
      language core;

      extend with #variants, #unit-type;

      fn main(ok : Bool) -> <| value : Nat, failure : Unit |> {
        return if ok then <| value = 0 |> else <| failure = unit |>
      }
    `);

    expectNoIssues(result);
  });

  test("rejects incompatible function-valued if branches before application", async () => {
    const result = await harness.parse(`
      language core;

      fn f(x : Nat) -> Nat {
        return succ(x)
      }

      fn g(k : fn(Nat) -> Nat) -> fn(Nat) -> Nat {
        return fn(x : Nat) {
          return k(k(x))
        }
      }

      fn main(n : Nat) -> Nat {
        return
          (if Nat::iszero(n)
            then f
            else g)(n)
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
