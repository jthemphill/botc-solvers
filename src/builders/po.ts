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
      ? game.constantBool(false)
      : game.not(priorPoChoice ?? game.constantBool(false));
  }

  record(timing: Timing, resolution: DeathAssignments, canChoose: BoolLike): void {
    const { game } = this;
    const poSources = [...resolution.bySource.keys()].filter((source) => source.kind === "po");
    const poKillAssignments = poSources.flatMap((source) => resolution.bySource.get(source) ?? []);
    const poDeathAssigned = game.anyOf(poKillAssignments);
    const poSourceAvailable = game.anyOf(poSources.map((source) => resolution.available.get(source) as BoolLike));
    const chargedPoAvailable = game.anyOf(
      poSources
        .filter((source) => source.targetCountWhenAvailable === 3)
        .map((source) => resolution.available.get(source) as BoolLike),
    );
    const poNonDeathTargetAvailable = game.anyOf(
      poSources.flatMap((source) => resolution.nonDeathTargets.get(source) ?? []),
    );
    const poChosePlayer = game.newBool();
    game.addImplication(poChosePlayer, poSourceAvailable);
    game.addImplication(poDeathAssigned, poChosePlayer);
    game.addImplication(chargedPoAvailable, poChosePlayer);
    game.addImplication(game.allOf([poChosePlayer, game.not(poDeathAssigned)]), poNonDeathTargetAvailable);
    // An Exorcist preserves the last choice instead of charging the Po.
    // https://wiki.bloodontheclocktower.com/index.php?title=Po&oldid=3104
    this.choices.set(
      timing,
      game.anyOf([
        game.allOf([canChoose, poChosePlayer]),
        game.allOf([game.not(canChoose), game.not(this.chargedAt(timing))]),
      ]),
    );
  }
}
