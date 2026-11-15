import { expect, test } from "bun:test";
import { BARE_CLAIM_TYPES, type Claim, type PuzzleDoc } from "../schema/puzzleDoc";
import { validatePuzzleDoc } from "../schema/validate";
import { CLAIM_EDITOR_CASES } from "./editorCases";
import { PUZZLE_EXAMPLES } from "./puzzleCatalog";

// The browser suite enters each claim of CLAIM_EDITOR_CASES in the editor and compares the export.
// This test makes sure that each catalog puzzle uses only the claim shapes of those cases.
// A shape is a claim type with one of its fields. A list with two or more entries is a different shape.

/** These fields have the same controls for all claim types. */
const SHARED_FIELDS = new Set([
  "roleTiming",
  "source",
  "alignment",
  "possibleActualRoles",
  "heardWidowCall",
  "knownEvilTwin",
  "nightwatchmanPings",
]);

function isRecord(value: unknown): value is Record<string, unknown> {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}

function fieldShapes(prefix: string, value: Record<string, unknown>, shapes: Set<string>): void {
  for (const [key, entry] of Object.entries(value)) {
    if (entry === undefined || key === "name" || key === "type") continue;
    const path = `${SHARED_FIELDS.has(key) ? "claim" : prefix}.${key}`;
    shapes.add(path);
    if (!Array.isArray(entry)) continue;
    if (entry.length >= 2) shapes.add(`${path}[2+]`);
    for (const item of entry) if (isRecord(item)) fieldShapes(`${path}[]`, item, shapes);
  }
}

function claimShapes(claim: Claim, shapes: Set<string>): void {
  // All claim types without reports have the same controls.
  const type = (BARE_CLAIM_TYPES as readonly string[]).includes(claim.type) ? "bare claim" : claim.type;
  shapes.add(type);
  const { gained, ...fields } = claim as Claim & { readonly gained?: Record<string, unknown> };
  fieldShapes(type, fields, shapes);
  if (gained === undefined) return;
  // The editor shows a gained ability with the controls of its own claim type.
  shapes.add("Philosopher.gained");
  claimShapes({ ...gained, name: claim.name } as Claim, shapes);
}

function docShapes(doc: PuzzleDoc): Set<string> {
  const shapes = new Set<string>();
  for (const claim of doc.claims) claimShapes(claim, shapes);
  return shapes;
}

test("each claim shape of the catalog has an editor case in the browser suite", () => {
  const covered = new Set<string>();
  for (const editorCase of CLAIM_EDITOR_CASES)
    for (const shape of docShapes(validatePuzzleDoc({ players: ["Ada", "Ben", "Cara"], ...editorCase })))
      covered.add(shape);

  const missing = new Map<string, string[]>();
  for (const example of PUZZLE_EXAMPLES)
    for (const shape of docShapes(validatePuzzleDoc(example.data)))
      if (!covered.has(shape)) missing.set(shape, [...(missing.get(shape) ?? []), example.id]);

  expect(Object.fromEntries([...missing].map(([shape, ids]) => [shape, ids.slice(0, 3)]))).toEqual({});
});
