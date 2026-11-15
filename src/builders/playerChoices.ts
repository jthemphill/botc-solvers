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

const CLAIM_ROLE_NAMES: Readonly<Record<string, string>> = {
  FortuneTeller: "Fortune Teller",
  VillageIdiot: "Village Idiot",
};
const PLAYER_FIELDS = ["player", "players", "left", "right", "among", "target"] as const;

function playersIn(entry: Readonly<Record<string, unknown>>): readonly string[] {
  return PLAYER_FIELDS.flatMap((field) => entry[field] ?? []).filter(
    (value): value is string => typeof value === "string",
  );
}

/**
 * Returns the players that a claim names, with the night of each report.
 * A claim names players in its own fields and in its lists of checks, choices, and guesses.
 * The caller uses a report only when the character has a night choice rule.
 */
function reportedChoices(claim: Claim): readonly ReportedChoice[] {
  const fields = claim as unknown as Readonly<Record<string, unknown>>;
  const role = CLAIM_ROLE_NAMES[claim.type] ?? claim.type;
  const lists = ["checks", "choices", "guesses"].flatMap((field) =>
    Array.isArray(fields[field]) ? [fields[field]] : [],
  );
  const seamstress = claim.type === "Philosopher" ? claim.seamstress : undefined;
  return [
    { role, timing: claim.timing, players: playersIn(fields) },
    ...lists.flatMap((list: readonly Readonly<Record<string, unknown>>[]) =>
      list.map((entry, index) => ({
        role,
        timing: (entry["timing"] as string | undefined) ?? `night_${index + 1}`,
        players: playersIn(entry),
      })),
    ),
    ...(seamstress === undefined
      ? []
      : [{ role: "Seamstress", timing: seamstress.timing ?? claim.timing, players: seamstress.among }]),
  ];
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
