import { choose } from "../model/actions";
import { CharacterType, roleCharacterType } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import { previousDayForNight } from "../model/timing";
import { isTimelineDeathEvent, type PuzzleDoc } from "../schema/puzzleDoc";
import { TimelineFacts } from "./timeline";

export function applyBarberSwaps(game: BOTCModel, doc: PuzzleDoc, facts: TimelineFacts): void {
  if (!doc.script.includes("Barber") || doc.setup === "atheist") return;
  for (const timing of facts.nights) {
    const deaths = (doc.timeline ?? []).filter(
      (event) =>
        isTimelineDeathEvent(event) && (event.timing === timing || event.timing === previousDayForNight(timing)),
    );
    const triggers = new Map<string, BoolLike>();
    for (const event of deaths) {
      const diedAtNight = event.timing === timing;
      for (const player of event.players) {
        const key = JSON.stringify([event.timing, player]);
        if (triggers.has(key)) continue;
        const role = diedAtNight
          ? game.characterBefore(player, "Barber", timing)
          : game.characterAt(player, "Barber", event.timing as Timing);
        const healthy = diedAtNight
          ? game.soberAndHealthyBeforeCharacterChange(player, timing)
          : game.soberAndHealthy(player, event.timing as Timing);
        triggers.set(key, game.allOf([role, healthy], `${key}_barber_died_healthy`));
      }
    }
    for (const [key, trigger] of triggers) {
      const actors = facts.livingAt(timing).filter((player) => !facts.nightDeaths(timing).has(player));
      const offer = choose(game, { rule: "Barber:demon", actor: key, timing, active: trigger, count: 1 }, actors);
      for (const [actor, selectedActor] of offer.choices) {
        const demonBefore = game.anyOf(
          [...game.characters]
            .filter(([, role]) => roleCharacterType(role) === CharacterType.Demon)
            .map(([role]) => game.characterBefore(actor, role, timing)),
          `${timing}_${actor}_demon_before_barber`,
        );
        game.addImplication(selectedActor, demonBefore);
        const swapping = game.newBool(`${key}_${actor}_accepts_barber_swap`);
        game.addImplication(swapping, selectedActor);
        const targets = choose(
          game,
          { rule: "Barber:players", actor, timing, active: swapping, count: 2 },
          doc.players,
        );
        for (const [player, selected] of targets.choices) {
          if (player === actor) continue;
          for (const [role, character] of game.characters) {
            if (roleCharacterType(character) === CharacterType.Demon)
              game.addImplication(selected, game.characterBefore(player, role, timing).not());
          }
        }
        for (const [player, selected] of targets.choices) {
          for (const [other, otherSelected] of targets.choices) {
            if (player === other) continue;
            for (const character of doc.script) {
              const active = game.allOf(
                [selected, otherSelected, game.characterBefore(other, character, timing)],
                `${key}_${actor}_${player}_receives_${other}_${character}`,
              );
              game.trace.replace({ player, character, timing, active, rule: "Barber" });
            }
          }
        }
      }
    }
  }
}
