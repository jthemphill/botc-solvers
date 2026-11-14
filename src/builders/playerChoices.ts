import { select } from "../model/actions";
import { roleNightChoice } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import { nightActionOrder } from "../model/nightOrder";
import type { Claim, PuzzleDoc } from "../schema/puzzleDoc";
import { resolveRoleRef } from "./roleRef";
import type { TimelineFacts } from "./timeline";

interface ChoiceDoc extends PuzzleDoc {
  readonly facts: TimelineFacts;
}

interface ReportedChoice {
  readonly role: string;
  readonly timing: string | undefined;
  readonly players: readonly string[];
}

/** Returns the night choices of players that a claim reports. */
function reportedChoices(claim: Claim): readonly ReportedChoice[] {
  const nightly = (index: number, timing: string | undefined) => timing ?? `night_${index + 1}`;
  switch (claim.type) {
    case "Acrobat":
      return (claim.choices ?? []).map((choice) => ({
        role: "Acrobat",
        timing: choice.timing,
        players: [choice.player],
      }));
    case "Chambermaid":
      return (claim.checks ?? []).map((check, index) => ({
        role: "Chambermaid",
        timing: nightly(index, check.timing),
        players: [check.left, check.right],
      }));
    case "Dreamer":
      return claim.player === undefined
        ? []
        : [{ role: "Dreamer", timing: nightly(0, claim.timing), players: [claim.player] }];
    case "Exorcist":
      return (claim.choices ?? []).map((choice) => ({
        role: "Exorcist",
        timing: choice.timing,
        players: [choice.player],
      }));
    case "FortuneTeller":
      return claim.checks.map((check, index) => ({
        role: "Fortune Teller",
        timing: nightly(index, check.timing),
        players: [check.left, check.right],
      }));
    case "Gambler":
      return (claim.guesses ?? []).map((guess) => ({ role: "Gambler", timing: guess.timing, players: [guess.player] }));
    case "Innkeeper":
      return (claim.choices ?? []).map((choice) => ({
        role: "Innkeeper",
        timing: choice.timing,
        players: choice.players,
      }));
    case "Philosopher":
      return claim.seamstress === undefined
        ? []
        : [
            {
              role: "Seamstress",
              timing: claim.seamstress.timing ?? claim.timing,
              players: claim.seamstress.among,
            },
          ];
    case "Professor":
      return claim.target === undefined ? [] : [{ role: "Professor", timing: claim.timing, players: [claim.target] }];
    case "Ravenkeeper":
      return claim.player === undefined ? [] : [{ role: "Ravenkeeper", timing: claim.timing, players: [claim.player] }];
    case "Sailor":
      return (claim.choices ?? []).map((choice) => ({
        role: "Sailor",
        timing: choice.timing,
        players: [choice.player],
      }));
    case "Seamstress":
      return [{ role: "Seamstress", timing: claim.timing, players: claim.among }];
    case "Snake Charmer":
      return claim.checks.map((check) => ({ role: "Snake Charmer", timing: check.timing, players: [check.player] }));
    case "VillageIdiot":
      return claim.checks.map((check, index) => ({
        role: "Village Idiot",
        timing: nightly(index, check.timing),
        players: [check.player],
      }));
    default:
      return [];
  }
}

/**
 * Makes a choice action for each character that has a night choice rule.
 * A reported choice fixes the targets of its night. A night without a report has an unknown choice.
 * Characters with other choice variables register their own choice actions.
 */
export function generateNightChoices(
  game: BOTCModel,
  doc: ChoiceDoc,
  diesBeforeInformation: (player: string, timing: Timing) => BoolLike,
): void {
  const reports = new Map<string, Set<string>>();
  for (const claim of doc.claims)
    for (const report of reportedChoices(claim)) {
      if (!/^night_\d+$/.test(report.timing ?? "") || report.players.length === 0) continue;
      const key = JSON.stringify([claim.name, report.role, report.timing]);
      const players = reports.get(key) ?? new Set<string>();
      for (const player of report.players) players.add(player);
      reports.set(key, players);
    }

  for (const role of doc.script) {
    const rule = roleNightChoice(resolveRoleRef(role));
    if (rule === undefined) continue;
    const usesByActor = new Map<string, BoolLike[]>();
    for (const timing of doc.facts.nights) {
      if (rule.nights === "exceptFirst" && timing === "night_1") continue;
      // A Demon kill occurs before the actions of the characters that follow the Moonchild in the night order.
      const actsAfterKills = nightActionOrder(role, timing) > nightActionOrder("Moonchild", timing);
      for (const actor of doc.facts.livingAt(timing)) {
        const scheduled =
          rule.nights === "whenKilledAtNight"
            ? game.constantBool(doc.facts.nightDeaths(timing).has(actor))
            : actsAfterKills
              ? game.not(diesBeforeInformation(actor, timing))
              : game.constantBool(true);
        const canAct = game.allOf([game.hasAbilityAt(actor, role, timing), scheduled]);
        const reported = reports.get(JSON.stringify([actor, role, timing]));
        let acts: BoolLike = canAct;
        if (rule.once === true && reported === undefined) {
          acts = game.newBool();
          game.addImplication(acts, canAct);
        }
        if (rule.once === true) usesByActor.set(actor, [...(usesByActor.get(actor) ?? []), acts]);
        const choices =
          reported === undefined
            ? select(game, doc.players, acts, rule.count)
            : new Map([...reported].map((player) => [player, acts]));
        game.registerChoiceAction({
          rule: `${role}:players`,
          actor,
          timing,
          active: acts,
          count: reported === undefined ? rule.count : choices.size,
          choices,
          ability: role,
        });
      }
    }
    for (const uses of usesByActor.values()) game.addEnforcedAtMostN(uses, 1, game.constantBool(true));
  }
}
