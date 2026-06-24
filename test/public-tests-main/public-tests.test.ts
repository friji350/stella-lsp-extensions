import { afterEach, beforeAll, describe, test } from "vitest";
import { readdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

import {
  StellaTestHarness,
  type StellaAnalysis,
} from "../utils/stella-test-harness.js";

interface PublicFixture {
  suiteName: string;
  caseName: string;
  inputPath: string;
  source: string;
  expectedTags: string[];
}

const fixturesRoot = path.dirname(fileURLToPath(import.meta.url));
const suiteNames = ["hw1", "hw2", "hw3"] as const;
const fixtureSuites = suiteNames.map((suiteName) => ({
  suiteName,
  fixtures: loadFixtures(suiteName),
}));

let harness: StellaTestHarness;

beforeAll(() => {
  harness = new StellaTestHarness();
});

afterEach(async () => {
  await harness.clear();
});

describe("public-tests-main", () => {
  for (const { suiteName, fixtures } of fixtureSuites) {
    describe(suiteName, () => {
      for (const fixture of fixtures) {
        test(fixture.caseName, async () => {
          const analysis = await harness.parse(fixture.source);
          assertFixture(fixture, analysis);
        });
      }
    });
  }
});

function loadFixtures(suiteName: string): PublicFixture[] {
  const suitePath = path.join(fixturesRoot, suiteName);

  return readdirSync(suitePath)
    .filter((fileName) => fileName.endsWith(".in"))
    .sort((left, right) => left.localeCompare(right, undefined, { numeric: true }))
    .map((inputFileName) => {
      const inputPath = path.join(suitePath, inputFileName);
      const outputPath = inputPath.replace(/\.in$/, ".out");
      const expectedTags = readExpectedTags(outputPath);

      return {
        suiteName,
        caseName: formatCaseName(inputFileName, expectedTags),
        inputPath,
        source: readFileSync(inputPath, "utf8"),
        expectedTags,
      };
    });
}

function readExpectedTags(outputPath: string): string[] {
  return readFileSync(outputPath, "utf8")
    .split(/\r?\n/u)
    .map((line) => line.trim())
    .filter((line) => line.startsWith("ERROR_"));
}

function formatCaseName(inputFileName: string, expectedTags: string[]): string {
  const baseName = inputFileName.replace(/\.in$/u, "");
  return expectedTags.length > 0
    ? `${baseName} -> ${expectedTags.join(", ")}`
    : `${baseName} -> OK`;
}

function assertFixture(
  fixture: PublicFixture,
  analysis: StellaAnalysis
): void {
  const context = [
    `Fixture: ${fixture.suiteName}/${path.basename(fixture.inputPath)}`,
    `Expected tags: ${
      fixture.expectedTags.length > 0 ? fixture.expectedTags.join(", ") : "<none>"
    }`,
    `Actual tags: ${
      analysis.errorTags.length > 0 ? analysis.errorTags.join(", ") : "<none>"
    }`,
    `Messages:`,
    analysis.allMessages.length > 0 ? analysis.allMessages.join("\n") : "<none>",
  ].join("\n");

  if (fixture.expectedTags.length === 0) {
    if (analysis.parserErrors.length > 0) {
      throw new Error(`Expected program to parse without errors.\n\n${context}`);
    }

    if (analysis.structuralErrors.length > 0) {
      throw new Error(`Expected a valid AST.\n\n${context}`);
    }

    if (analysis.diagnostics.length > 0) {
      throw new Error(`Expected no diagnostics.\n\n${context}`);
    }

    return;
  }

  if (!analysis.hasErrors) {
    throw new Error(`Expected at least one typing or validation error.\n\n${context}`);
  }

  if (analysis.errorTags.length === 0) {
    return;
  }

  const matchesExpectedTag = analysis.errorTags.some((tag) =>
    fixture.expectedTags.includes(tag)
  );

  if (!matchesExpectedTag) {
    throw new Error(`Actual error tags do not match expected ones.\n\n${context}`);
  }
}
