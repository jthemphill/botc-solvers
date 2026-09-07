import { type BooleanConstraints, type BoolLike } from "../model/boolean";
import { previousNight, type Timing } from "../model/timing";
import type { DeathAssignments } from "./nightDeaths";

export class PoChoices {
  private readonly choices = new Map<Timing, BoolLike>();
  constructor(private readonly game: BooleanConstraints) {}

  chargedAt(timing: Timing): BoolLike {
    const { game } = this;
    const priorNight = previousNight(timing);
    const priorPoChoice = priorNight === undefined ? undefined : this.choices.get(priorNight);
    return priorNight === undefined || priorNight === "night_1"
      ? game.constantBool(false, `${timing}_po_cannot_be_charged`)
      : game.not(priorPoChoice ?? game.constantBool(false, `${timing}_no_prior_po_choice`), `${timing}_po_charged`);
  }

  record(timing: Timing, resolution: DeathAssignments): void {
    const { game } = this;
    const poSources = [...resolution.bySource.keys()].filter((source) => source.kind === "po");
    const poKillAssignments = poSources.flatMap((source) => resolution.bySource.get(source) ?? []);
    const poDeathAssigned = game.anyOf(poKillAssignments, `${timing}_po_death_assigned`);
    const poSourceAvailable = game.anyOf(
      poSources.map((source) => resolution.available.get(source) as BoolLike),
      `${timing}_po_source_available`,
    );
    const chargedPoAvailable = game.anyOf(
      poSources
        .filter((source) => source.targetCountWhenAvailable === 3)
        .map((source) => resolution.available.get(source) as BoolLike),
      `${timing}_charged_po_available`,
    );
    const poNonDeathTargetAvailable = game.anyOf(
      poSources.flatMap((source) => resolution.nonDeathTargets.get(source) ?? []),
      `${timing}_po_non_death_target_available`,
    );
    const poChosePlayer = game.newBool(`${timing}_po_chose_player`);
    game.addImplication(poChosePlayer, poSourceAvailable);
    game.addImplication(poDeathAssigned, poChosePlayer);
    game.addImplication(chargedPoAvailable, poChosePlayer);
    game.addImplication(
      game.allOf(
        [poChosePlayer, game.not(poDeathAssigned, `${timing}_po_choice_caused_no_death`)],
        `${timing}_po_chose_without_a_death`,
      ),
      poNonDeathTargetAvailable,
    );
    this.choices.set(timing, poChosePlayer);
  }
}
