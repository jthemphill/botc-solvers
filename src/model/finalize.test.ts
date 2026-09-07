import { beforeAll, expect, test } from "bun:test";
import { BOTCModel, night } from "./model";
import { roleByName } from "./roleRegistry";
import { KissatBackend } from "./sat";

let backend: KissatBackend;
beforeAll(async () => {
  backend = await KissatBackend.create();
});

test("health dependencies constrain abilities introduced during finalization", async () => {
  for (const declareAbilityFirst of [false, true]) {
    for (const healthy of [false, true]) {
      const game = new BOTCModel(["A", "B"], { characters: ["Chef", "No Dashii"].map(roleByName), backend });
      game.fixActual("A", "Chef");
      game.fixActual("B", "No Dashii");
      if (declareAbilityFirst) game.hasAbilityAt("B", "No Dashii", night(2));
      const query = game.soberAndHealthyBeforeOwnPoisoning("A", night(2), [], "health");
      game.addTruth(healthy ? query : query.not());
      expect((await game.solve()).status).toBe(healthy ? "unsat" : "sat");
      expect(game.finalize()).toBe(game.finalize());
    }
  }
});

test("source registration order does not change health or wake queries", async () => {
  for (const sourcesFirst of [false, true]) {
    const game = new BOTCModel(["A"], { characters: [roleByName("Chef")], backend });
    const own = game.constantBool(true, "own_drunking");
    const addSources = () => {
      game.addTimedDrunkSource("A", [night(2)], own);
      game.preventWakeAt("A", night(2), own);
    };
    if (sourcesFirst) addSources();
    const beforeOwn = game.soberAndHealthyBeforeOwnDrunking("A", night(2), [own], "before_own");
    const afterOwn = game.soberAndHealthy("A", night(2));
    const prevented = game.wakePreventedAt("A", night(2), "wake_prevented");
    if (!sourcesFirst) addSources();
    game.addTruth(beforeOwn);
    game.addFalse(afterOwn);
    game.addTruth(prevented);
    expect((await game.solve()).status).toBe("sat");
    expect(() => game.preventWakeAt("A", night(3), own)).toThrow("finalized");
  }
});
