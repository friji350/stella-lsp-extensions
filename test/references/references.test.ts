import { afterEach, describe, expect, test } from "vitest";

import { StellaTestHarness, type StellaAnalysis } from "../utils/stella-test-harness.js";

const harness = new StellaTestHarness();

afterEach(async () => {
  await harness.clear();
});

describe("References", () => {
  test("accepts allocation, assignment, dereference, and sequencing", async () => {
    const result = await harness.parse(`
      language core;

      extend with #unit-type, #references, #sequencing;

      fn inc_ref(ref : &Nat) -> Unit {
        return ref := succ(*ref)
      }

      fn inc3(ref : &Nat) -> Nat {
        return
          inc_ref(ref);
          inc_ref(ref);
          inc_ref(ref);
          *ref
      }

      fn main(n : Nat) -> Nat {
        return inc3(new(n))
      }
    `);

    expectNoIssues(result);
  });

  test("uses expected type information for memory address literals", async () => {
    const result = await harness.parse(`
      language core;

      extend with #references, #type-ascriptions;

      fn read(ref : &Nat) -> Nat {
        return *ref
      }

      fn main(n : Nat) -> Nat {
        return read(<0xABCDEF>)
      }
    `);

    expectNoIssues(result);
  });

  test("rejects dereferencing a non-reference value", async () => {
    const result = await harness.parse(`
      language core;

      extend with #references;

      fn main(n : Nat) -> Nat {
        return *0
      }
    `);

    expectCleanSyntax(result);
    expect(result.allMessages.join("\n")).toContain(
      "Dereference expects a reference"
    );
  });

  test("rejects assignment to a non-reference value", async () => {
    const result = await harness.parse(`
      language core;

      extend with #references;

      fn main(n : Nat) -> Nat {
        return 0 := succ(0)
      }
    `);

    expectCleanSyntax(result);
    expect(result.allMessages.join("\n")).toContain(
      "Assignment expects a reference"
    );
  });
});

function expectNoIssues(result: StellaAnalysis): void {
  expect(result.allMessages.join("\n")).toBe("");
  expect(result.hasErrors).toBe(false);
}

function expectCleanSyntax(result: StellaAnalysis): void {
  expect([...result.parserErrors, ...result.structuralErrors]).toHaveLength(0);
}
