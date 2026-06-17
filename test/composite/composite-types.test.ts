import { afterEach, describe, expect, test } from "vitest";

import { StellaTestHarness, type StellaAnalysis } from "../utils/stella-test-harness.js";

const harness = new StellaTestHarness();

afterEach(async () => {
  await harness.clear();
});

describe("Composite types and patterns", () => {
  test("accepts records containing tuples and projects nested fields", async () => {
    const result = await harness.parse(`
      language core;

      extend with #records, #tuples;

      fn main(n : Nat) -> Nat {
        return { pair = {n, succ(n)} }.pair.2
      }
    `);

    expectNoIssues(result);
  });

  test("accepts list construction and list operations", async () => {
    const result = await harness.parse(`
      language core;

      extend with #lists, #type-ascriptions;

      fn main(n : Nat) -> Nat {
        return List::head(cons(n, [] as [Nat]))
      }
    `);

    expectNoIssues(result);
  });

  test("accepts structural list patterns", async () => {
    const result = await harness.parse(`
      language core;

      extend with #lists, #structural-patterns;

      fn head_or_zero(xs : [Nat]) -> Nat {
        return match xs {
          [] => 0
        | cons(x, rest) => x
        }
      }

      fn main(n : Nat) -> Nat {
        return head_or_zero(cons(n, []))
      }
    `);

    expectNoIssues(result);
  });

  test("accepts sum values and sum patterns", async () => {
    const result = await harness.parse(`
      language core;

      extend with #sum-types, #unit-type;

      fn unwrap(value : Nat + Unit) -> Nat {
        return match value {
          inl(n) => n
        | inr(_) => 0
        }
      }

      fn main(n : Nat) -> Nat {
        return unwrap(inl(n))
      }
    `);

    expectNoIssues(result);
  });

  test("accepts variants and variant patterns", async () => {
    const result = await harness.parse(`
      language core;

      extend with #variants, #unit-type;

      fn attempt(ok : Bool) -> <| value : Nat, failure : Unit |> {
        return
          if ok
            then <| value = 0 |>
            else <| failure = unit |>
      }

      fn main(ok : Bool) -> Nat {
        return match attempt(ok) {
          <| value = n |> => succ(n)
        | <| failure = f |> => 0
        }
      }
    `);

    expectNoIssues(result);
  });

  test("rejects a record value missing a required field", async () => {
    const result = await harness.parse(`
      language core;

      extend with #records, #structural-subtyping;

      fn main(n : Nat) -> { x : Nat, y : Bool } {
        return { x = n }
      }
    `);

    expectCleanSyntax(result);
    expect(result.errorTags).toContain("ERROR_MISSING_RECORD_FIELDS");
  });
});

function expectNoIssues(result: StellaAnalysis): void {
  expect(result.allMessages.join("\n")).toBe("");
  expect(result.hasErrors).toBe(false);
}

function expectCleanSyntax(result: StellaAnalysis): void {
  expect([...result.parserErrors, ...result.structuralErrors]).toHaveLength(0);
}
