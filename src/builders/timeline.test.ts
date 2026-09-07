import { expect, test } from "bun:test";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { TimelineFacts } from "./timeline";

const doc: PuzzleDoc = { players: ["A", "B", "C", "D"], script: [], claims: [] };

test("missing and complete empty reports remain distinct", () => {
  const facts = new TimelineFacts({ ...doc, timeline: [{ type: "nightDeath", timing: "night_2", players: [] }] });
  expect(facts.reportedPlayers("nightDeath", "night_1")).toBeUndefined();
  expect([...facts.reportedPlayers("nightDeath", "night_2")!]).toEqual([]);
});

test("reported life and neighbors follow death and resurrection boundaries", () => {
  const facts = new TimelineFacts({
    ...doc,
    timeline: [
      { type: "execution", timing: "day_1", players: ["B"] },
      { type: "nightDeath", timing: "night_2", players: ["D"] },
      { type: "resurrection", timing: "night_2", players: ["B"] },
    ],
  });
  expect(facts.livingAt("day_1")).toEqual(doc.players);
  expect(facts.livingAt("night_2")).toEqual(["A", "C", "D"]);
  expect(facts.neighbors("A", facts.deadBefore("night_2"))).toEqual(["D", "C"]);
  expect(facts.livingAt("day_2")).toEqual(["A", "B", "C"]);
  expect(facts.finalLiving).toEqual(["A", "B", "C"]);
});

test("duplicate reports and renaming preserve observed life with seating intact", () => {
  const event = { type: "nightDeath" as const, timing: "night_2", players: ["B"] };
  const once = new TimelineFacts({ ...doc, timeline: [event] });
  const twice = new TimelineFacts({ ...doc, timeline: [event, event] });
  const renamed = new TimelineFacts({
    ...doc,
    players: doc.players.map((p) => `seat-${p}`),
    timeline: [{ ...event, players: ["seat-B"] }],
  });
  expect(twice.livingAt("day_2")).toEqual(once.livingAt("day_2"));
  expect(renamed.livingAt("day_2")).toEqual(once.livingAt("day_2").map((p) => `seat-${p}`));
});

test("default report times determine the horizon without titles or player names", () => {
  const facts = new TimelineFacts({
    ...doc,
    title: "day_99",
    claims: [
      { type: "Legionary", name: "night_80", counts: [{ count: 0 }, { count: 1 }] },
      { type: "Juggler", name: "A", guesses: {}, correctCount: 0 },
    ],
  });
  expect(facts.timings).toEqual(["night_1", "night_2"]);
  expect(facts.nights).toEqual(["night_1", "night_2"]);
  expect(facts.previousTiming("day_2")).toBe("night_2");
});
