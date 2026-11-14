import type { BoolVar } from "../model/boolean";
import { CharacterType, roleCharacterType } from "../model/core";
import type { BoolLike, BOTCModel, Timing } from "../model/model";
import { nightActionOrder } from "../model/nightOrder";
import { previousNight } from "../model/timing";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import { resolveRoleRef } from "./roleRef";
import type { TimelineFacts } from "./timeline";

interface GoonDoc extends PuzzleDoc {
  readonly facts: TimelineFacts;
}

/** These Demons have their own choice variables or make no night choice. */
const DEMONS_WITHOUT_GENERIC_CHOICE = new Set(["Pukka", "Shabaloth", "Leviathan"]);

function dayOf(night: Timing): Timing {
  return night.replace("night_", "day_") as Timing;
}

/**
 * Applies the Goon ability to the registered player choices.
 * Each night, the first player that chooses the Goon is drunk until dusk.
 * The Goon gets the alignment of that player.
 *
 * Other rules can ask questions before all choices are registered.
 * `resolve` gives the answers their values.
 */
export class GoonRule {
  readonly inPlay: boolean;
  private readonly firstChoices = new Map<string, BoolVar>();
  private readonly goodAt = new Map<string, BoolVar>();
  private readonly chosenBeforeQueries: { timing: Timing; order: number; answer: BoolVar }[] = [];

  constructor(
    private readonly game: BOTCModel,
    private readonly doc: GoonDoc,
  ) {
    this.inPlay = doc.script.includes("Goon") && doc.setup !== "atheist";
    if (!this.inPlay) return;
    for (const night of doc.facts.nights)
      for (const player of doc.players) {
        const good = game.newBool();
        this.goodAt.set(`${player}\u0000${night}`, good);
        game.setGoodAt(player, night, good);
        game.setGoodAt(player, dayOf(night), good);
      }
    this.registerDemonChoices();
  }

  /** Is true when the actor is the first player that chooses the Goon on this night. */
  firstChoiceBy(actor: string, night: Timing): BoolLike {
    if (!this.inPlay) return this.game.constantBool(false);
    const key = `${actor}\u0000${night}`;
    let first = this.firstChoices.get(key);
    if (first === undefined) {
      first = this.game.newBool();
      this.firstChoices.set(key, first);
      this.game.addTimedDrunkSource(actor, [night, dayOf(night)], first);
    }
    return first;
  }

  /** Is true when a holder of the role is the first player that chooses the Goon on this night. */
  firstChoiceByRole(role: string, night: Timing): BoolLike {
    if (!this.inPlay) return this.game.constantBool(false);
    return this.game.anyOf(
      this.doc.facts
        .livingAt(night)
        .map((actor) =>
          this.game.allOf([this.firstChoiceBy(actor, night), this.game.hasAbilityAt(actor, role, night)]),
        ),
    );
  }

  /** Is true when a player chose the Goon before the given position in the night order. */
  chosenBefore(night: Timing, order: number): BoolLike {
    if (!this.inPlay) return this.game.constantBool(false);
    const answer = this.game.newBool();
    this.chosenBeforeQueries.push({ timing: night, order, answer });
    return answer;
  }

  /**
   * Adds the choice of a Demon that chooses the Goon first.
   * This Demon is drunk and kills nobody. A Demon kill is a different registered choice.
   */
  private registerDemonChoices(): void {
    const { game, doc } = this;
    const demons = doc.script.filter(
      (role) =>
        roleCharacterType(resolveRoleRef(role)) === CharacterType.Demon && !DEMONS_WITHOUT_GENERIC_CHOICE.has(role),
    );
    for (const night of doc.facts.nights) {
      if (night === "night_1") continue;
      const living = doc.facts.livingAt(night);
      for (const role of demons)
        for (const actor of living)
          for (const target of living) {
            if (target === actor) continue;
            const chosen = game.newBool();
            game.addImplication(chosen, game.hasAbilityAt(actor, role, night));
            game.addImplication(chosen, game.hasAbilityAt(target, "Goon", night));
            game.addImplication(chosen, game.not(this.chosenBefore(night, nightActionOrder(role, night))));
            game.registerPlayerChoice({ actor, role, target, timing: night, chosen });
          }
    }
  }

  /** Reads all registered player choices. Call this after the last choice is registered. */
  resolve(): void {
    if (!this.inPlay) return;
    const { game, doc } = this;
    for (const night of doc.facts.nights) {
      const living = new Set(doc.facts.livingAt(night));
      const choices = game
        .playerChoices()
        .filter((choice) => choice.timing === night && living.has(choice.target))
        .map((choice) => ({ ...choice, order: nightActionOrder(choice.role, night) }))
        .sort((left, right) => left.order - right.order);

      const firstByActor = new Map<string, BoolLike[]>();
      const firstByGoon = new Map<string, { actor: string; first: BoolLike }[]>();
      const choicesOfGoon: { order: number; choosesGoon: BoolLike }[] = [];
      let chosenEarlier: BoolLike = game.constantBool(false);
      for (const choice of choices) {
        const choosesGoon = game.allOf([choice.chosen, game.hasAbilityAt(choice.target, "Goon", night)]);
        const first = game.allOf([choosesGoon, game.not(chosenEarlier)]);
        chosenEarlier = game.anyOf([chosenEarlier, choosesGoon]);
        choicesOfGoon.push({ order: choice.order, choosesGoon });
        firstByActor.set(choice.actor, [...(firstByActor.get(choice.actor) ?? []), first]);
        firstByGoon.set(choice.target, [...(firstByGoon.get(choice.target) ?? []), { actor: choice.actor, first }]);
      }

      for (const actor of firstByActor.keys()) this.firstChoiceBy(actor, night);
      for (const [key, first] of this.firstChoices) {
        const [actor, timing] = key.split("\u0000") as [string, Timing];
        if (timing === night) game.equate(first, game.anyOf(firstByActor.get(actor) ?? []));
      }
      for (const query of this.chosenBeforeQueries) {
        if (query.timing !== night) continue;
        const earlier = choicesOfGoon.filter((choice) => choice.order < query.order);
        game.equate(query.answer, game.anyOf(earlier.map((choice) => choice.choosesGoon)));
      }

      const priorNight = previousNight(night);
      const wasGood = (player: string): BoolLike =>
        priorNight === undefined ? game.isGood(player) : game.isGoodAt(player, priorNight);
      for (const player of doc.players) {
        const firstChoices = firstByGoon.get(player) ?? [];
        const turnsGood = game.anyOf(firstChoices.map(({ actor, first }) => game.allOf([first, wasGood(actor)])));
        const turnsEvil = game.anyOf(
          firstChoices.map(({ actor, first }) => game.allOf([first, game.not(wasGood(actor))])),
        );
        game.equate(
          this.goodAt.get(`${player}\u0000${night}`) as BoolVar,
          game.anyOf([turnsGood, game.allOf([wasGood(player), game.not(turnsEvil)])]),
        );
      }
    }
  }
}
