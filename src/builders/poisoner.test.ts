import { beforeAll, expect, test } from "bun:test";
import { buildFromDoc } from "./buildFromDoc";
import { KissatBackend } from "../model/sat";
import { validatePuzzleDoc } from "../schema/validate";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

// One Poisoner choice lasts through the night and the following day.
// Poison ends when the source loses the Poisoner character.
// https://wiki.bloodontheclocktower.com/index.php?title=Poisoner&oldid=1737
function scenario(artistAnswer: string) {
  return {
    players: ["A", "B", "C", "D", "E"],
    script: ["Artist", "Ravenkeeper", "Poisoner", "Imp", "Chef"],
    setup: "none",
    timeline: [{ type: "nightDeath", timing: "night_2", players: ["B"] }],
    claims: [
      {
        type: "Artist",
        name: "A",
        possibleActualRoles: ["Artist"],
        timing: "day_2",
        info: [{ timing: "day_2", expression: artistAnswer }],
      },
      {
        type: "Ravenkeeper",
        name: "B",
        possibleActualRoles: ["Ravenkeeper"],
        timing: "night_2",
        player: "A",
        role: "Imp",
      },
      { type: "Poisoner", name: "C", possibleActualRoles: ["Poisoner"] },
      { type: "Imp", name: "D", possibleActualRoles: ["Imp"] },
      { type: "Chef", name: "E", possibleActualRoles: ["Chef"] },
    ],
  };
}

test("a Poisoner cannot give two players false information in the same night and day", async () => {
  for (const artistCorrect of [false, true]) {
    const game = buildFromDoc(
      validatePuzzleDoc(scenario(artistCorrect ? "C.role == Poisoner" : "C.role == Imp")),
      backend,
    );
    expect(await game.solveAll()).toHaveLength(artistCorrect ? 1 : 0);
  }
});

test("poison persists through the day and a new target can be chosen next night", async () => {
  const doc = scenario("C.role == Poisoner");
  doc.claims[0]!.info!.push({ timing: "day_3", expression: "C.role == Poisoner" });
  const game = buildFromDoc(validatePuzzleDoc(doc), backend);
  game.addTruth(game.poisoned("B", "day_2"));
  game.addTruth(game.poisoned("A", "night_3"));
  game.addTruth(game.poisoned("A", "day_3"));
  expect(await game.solveAll()).toHaveLength(1);
});

test("poison ends after an Imp starpass to the Poisoner", async () => {
  const doc = scenario("C.role == Imp");
  doc.timeline[0]!.players = ["D"];
  doc.claims[1] = { type: "Ravenkeeper", name: "B", possibleActualRoles: ["Ravenkeeper"] };
  const game = buildFromDoc(validatePuzzleDoc(doc), backend);
  game.addTruth(game.characterAt("C", "Imp", "day_2"));
  game.addTruth(game.poisoned("A", "day_2"));
  expect(await game.solveAll()).toHaveLength(0);
});
