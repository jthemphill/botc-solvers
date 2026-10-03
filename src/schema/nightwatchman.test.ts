import { expect, test } from "bun:test";
import { validatePuzzleDoc } from "./validate";
import { docReducer } from "../state/puzzleDoc";
import { protectedScriptRoles } from "../state/scriptRoles";
import { claimSummary } from "../components/claimSummary";

const input = {
  players: ["A", "B", "C"],
  script: ["Philosopher", "Chef", "Nightwatchman"],
  claims: [
    {
      type: "Philosopher",
      name: "A",
      timing: "night_1",
      role: "Nightwatchman",
      nightwatchman: { chosen: "B", timing: "night_2" },
    },
    { type: "Chef", name: "C", nightwatchmanPings: [{ player: "B", timing: "night_2" }] },
  ],
};

test("Nightwatchman choices and received information survive validation and renaming", () => {
  const doc = validatePuzzleDoc(input);
  expect(JSON.parse(JSON.stringify(doc))).toEqual(input);
  const renamed = docReducer(doc, { type: "renamePlayer", index: 1, name: "Bea" });
  expect(renamed.claims[0]).toMatchObject({ nightwatchman: { chosen: "Bea", timing: "night_2" } });
  expect(renamed.claims[1]?.nightwatchmanPings).toEqual([{ player: "Bea", timing: "night_2" }]);
  expect(claimSummary(renamed.claims[0]!)).toContain("chose Bea");
  expect(claimSummary(renamed.claims[1]!)).toContain("learned Bea is the Nightwatchman");
  const removed = docReducer(renamed, { type: "removePlayer", index: 1 });
  expect(removed.claims[0]).toMatchObject({ nightwatchman: undefined });
  expect(removed.claims[1]?.nightwatchmanPings).toBeUndefined();
});

test("received Nightwatchman information protects its ability in the script", () => {
  const doc = validatePuzzleDoc({ ...input, claims: [input.claims[1]] });
  expect(protectedScriptRoles(doc)).toContain("Nightwatchman");
});

test.each([
  { nightwatchmanPings: "B" },
  { nightwatchmanPings: [{ player: 1, timing: "night_1" }] },
  { nightwatchmanPings: [{ player: "B", timing: "night_0" }] },
  { nightwatchman: { chosen: false } },
  { nightwatchman: { chosen: "B", timing: "soon" } },
])("rejects malformed Nightwatchman reports: %j", (fields) => {
  expect(() => validatePuzzleDoc({ ...input, claims: [{ ...input.claims[0], ...fields }] })).toThrow();
});
