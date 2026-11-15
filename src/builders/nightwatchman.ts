import { choose, type ChoiceAction } from "../model/actions";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import { timingOrder } from "../model/timing";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { BuildClaim } from "./philosopher";
import type { TimelineFacts } from "./timeline";

interface Signal {
  readonly target: ChoiceAction;
  readonly shown: ChoiceAction;
}

// A healthy Nightwatchman sends information to the chosen player.
// A Vortox changes the information, but does not change the recipient.
// https://wiki.bloodontheclocktower.com/index.php?title=Nightwatchman&oldid=2827
// https://wiki.bloodontheclocktower.com/index.php?title=Vortox&oldid=3017
export function applyNightwatchmanActions(
  game: BOTCModel,
  doc: Omit<PuzzleDoc, "claims"> & { readonly claims: readonly BuildClaim[] },
  facts: TimelineFacts,
): void {
  const signals = new Map<Timing, Map<string, Signal>>();
  if (doc.script.includes("Nightwatchman")) {
    game.withProvenance(
      {
        kind: "rule",
        id: "Nightwatchman.signals",
        source: "https://wiki.bloodontheclocktower.com/index.php?title=Nightwatchman&oldid=2827",
      },
      () => {
        for (const timing of facts.nights) {
          const byActor = new Map<string, Signal>();
          signals.set(timing, byActor);
          const vortox = doc.script.includes("Vortox")
            ? game.roleSoberAndHealthyAt("Vortox", timing)
            : game.constantBool(false);
          for (const actor of facts.livingAt(timing)) {
            const used = game.newBool();
            game.addImplication(used, game.hasAbilityAt(actor, "Nightwatchman", timing));
            const target = choose(
              game,
              { rule: "Nightwatchman:target", actor, timing, active: used, count: 1, ability: "Nightwatchman" },
              doc.players,
            );
            game.registerAbilityUse(actor, "Nightwatchman", timing, used);
            const sends = game.allOf([used, game.soberAndHealthy(actor, timing)]);
            const shown = choose(
              game,
              { rule: "Nightwatchman:shown", actor, timing, active: sends, count: 1 },
              doc.players,
            );
            game.addImplication(game.allOf([sends, vortox.not()]), shown.choices.get(actor)!);
            game.addImplication(game.allOf([sends, vortox]), game.not(shown.choices.get(actor)!));
            byActor.set(actor, { target, shown });
          }
        }
        game.enforceAbilityUseLimit("Nightwatchman", 1);
      },
    );
  }

  const falseInfo = () => game.constantBool(false);
  const received = (recipient: string, shown: string, timing: Timing): BoolLike => {
    if (!doc.players.includes(recipient) || !doc.players.includes(shown))
      throw new Error("Unknown player in Nightwatchman report.");
    return game.anyOf(
      [...(signals.get(timing)?.values() ?? [])].map((signal) =>
        game.allOf([signal.target.choices.get(recipient)!, signal.shown.choices.get(shown)!]),
      ),
    );
  };
  const honest = (player: string): BoolLike => {
    const timing = facts.timings.at(-1) ?? "night_1";
    return game.allOf([
      game.isGoodAt(player, timing),
      ...(doc.script.includes("Mutant") && facts.finalLiving.includes(player)
        ? [game.characterAt(player, "Mutant", timing).not()]
        : []),
    ]);
  };
  for (const [index, claim] of doc.claims.entries()) {
    game.withProvenance({ kind: "assumption", id: `claims[${index}]`, source: claim.source }, () => {
      const choice = claim.type === "Nightwatchman" ? claim : undefined;
      if (choice?.chosen) {
        const timing = (choice.timing ?? claim.timing ?? "night_1") as Timing;
        if (claim.gainedByPhilosopher !== undefined) {
          // The Philosopher must gain the ability before using it.
          // https://wiki.bloodontheclocktower.com/index.php?title=Philosopher&oldid=2421
          game.addImplication(
            game.allOf([honest(claim.name), game.actualIs(claim.name, "Philosopher")]),
            game.constantBool(
              timingOrder(timing) >= timingOrder((claim.gainedByPhilosopher.timing ?? "night_1") as Timing),
            ),
          );
        }
        const signal = signals.get(timing)?.get(claim.name);
        const possesses = game.hasAbilityAt(claim.name, "Nightwatchman", timing);
        game.addImplication(
          game.allOf([honest(claim.name), possesses]),
          signal?.target.choices.get(choice.chosen) ?? falseInfo(),
        );
        if (claim.type === "Nightwatchman" && claim.learned !== undefined) {
          const correctSignal =
            signal === undefined
              ? falseInfo()
              : game.allOf([
                  signal.target.choices.get(choice.chosen) ?? falseInfo(),
                  signal.shown.choices.get(claim.name)!,
                ]);
          if (!claim.learned) game.addImplication(possesses, game.not(correctSignal));
          if (claim.learned && claim.confirmedByChosen) {
            game.addImplication(honest(choice.chosen), received(choice.chosen, claim.name, timing));
          }
        }
      }
      for (const ping of claim.nightwatchmanPings ?? []) {
        game.addImplication(honest(claim.name), received(claim.name, ping.player, ping.timing as Timing));
      }
    });
  }
}
