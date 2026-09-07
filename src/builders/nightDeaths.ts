import { type BooleanConstraints, type BoolLike, type BoolVar } from "../model/boolean";
import { type Timing } from "../model/timing";
import { addMapValue, slug } from "../model/keys";

export interface NightDeathSource {
  readonly id: string;
  readonly available: BoolLike;
  readonly players?: readonly string[];
  readonly maxAssignments?: number;
  readonly targetCountWhenAvailable?: number;
  readonly requiredWhenAvailable?: boolean;
  readonly kind?: "demon" | "po";
  readonly succession?: readonly ("Imp" | "Fang Gu")[];
  readonly deathTiming?: "beforeInfo" | "afterInfo";
  readonly resolutionOrder?: number;
  readonly requiresAliveAtResolution?: string;
  readonly bypassesProtection?: boolean;
  readonly requiresDemonKillOf?: string;
  readonly constrainAssignment?: (player: string, assignment: BoolLike) => void;
}

export interface AssignedDeath {
  readonly player: string;
  readonly source: NightDeathSource;
  readonly value: BoolLike;
}

export class DeathAssignments {
  readonly deaths: AssignedDeath[] = [];
  readonly bySource = new Map<NightDeathSource, BoolLike[]>();
  readonly demonKills = new Map<string, BoolLike[]>();
  readonly available = new Map<NightDeathSource, BoolLike>();
  readonly nonDeathTargets = new Map<NightDeathSource, readonly BoolLike[]>();

  constructor(
    private readonly game: BooleanConstraints,
    private readonly timing: Timing,
    private readonly players: readonly string[],
    private readonly deadAtStart: ReadonlySet<string>,
  ) {}

  assign(player: string, source: NightDeathSource): BoolVar {
    const value = this.game.newBool(`${this.timing}_${player}_death_from_${source.id}`);
    this.game.addImplication(value, source.available);
    addMapValue(this.bySource, source, value);
    if (source.kind !== undefined) addMapValue(this.demonKills, player, value);
    this.deaths.push({ player, source, value });
    return value;
  }

  private earlierDeath(player: string, source: NightDeathSource): BoolVar {
    return this.game.anyOf(
      this.deaths
        .filter(
          (death) =>
            death.player === player &&
            (death.source.resolutionOrder ?? Infinity) < (source.resolutionOrder ?? Infinity),
        )
        .map((death) => death.value),
      `${this.timing}_${player}_dies_before_${source.id}`,
    );
  }

  constrainSources(): void {
    const { game, timing } = this;
    const sourceCapacityActive = game.constantBool(true, `${timing}_night_death_source_capacity_active`);
    for (const [source, assignments] of this.bySource) {
      game.addEnforcedAtMostN(assignments, source.maxAssignments ?? 1, sourceCapacityActive);
      const sourceAssigned =
        assignments.length === 1
          ? (assignments[0] as BoolLike)
          : game.anyOf(assignments, `${timing}_${source.id}_assigned`);
      let effectiveAvailability = source.available;
      if (source.requiresAliveAtResolution !== undefined) {
        const actor = source.requiresAliveAtResolution;
        const aliveAtPhaseStart = game.constantBool(
          this.players.includes(actor) && !this.deadAtStart.has(actor),
          `${timing}_${slug(actor)}_alive_at_phase_start_for_${slug(source.id)}`,
        );
        const diesEarlier = this.earlierDeath(actor, source);
        effectiveAvailability = game.allOf(
          [
            source.available,
            aliveAtPhaseStart,
            game.not(diesEarlier, `${timing}_${slug(actor)}_survives_until_${slug(source.id)}`),
          ],
          `${timing}_${slug(source.id)}_effective_availability`,
        );
        for (const assignment of assignments) game.addImplication(assignment, effectiveAvailability);
      }
      this.available.set(source, effectiveAvailability);
      if (source.requiredWhenAvailable !== false) game.addImplication(effectiveAvailability, sourceAssigned);
    }
  }

  constrainTargets(protectionAt: (player: string) => BoolLike): void {
    const { game, timing } = this;
    const deadAtPhaseStart = this.deadAtStart;
    for (const [source, assignments] of this.bySource) {
      if (source.kind === undefined) continue;
      const nonDeathTargets = this.players.map((player) => {
        const killedBySource = game.anyOf(
          this.deaths.filter((death) => death.player === player && death.source === source).map((death) => death.value),
          `${timing}_${slug(source.id)}_does_not_kill_${slug(player)}`,
        );
        const diesEarlier = this.earlierDeath(player, source);
        const survivesDemonTarget = game.anyOf(
          [
            game.constantBool(
              deadAtPhaseStart.has(player),
              `${timing}_${slug(player)}_dead_before_${slug(source.id)}_targets`,
            ),
            diesEarlier,
            protectionAt(player),
          ],
          `${timing}_${slug(player)}_can_survive_${slug(source.id)}_target`,
        );
        return game.allOf(
          [
            survivesDemonTarget,
            game.not(killedBySource, `${timing}_${slug(source.id)}_does_not_also_target_${slug(player)}`),
          ],
          `${timing}_${slug(player)}_non_death_target_for_${slug(source.id)}`,
        );
      });
      this.nonDeathTargets.set(source, nonDeathTargets);
      if (source.targetCountWhenAvailable !== undefined) {
        game.addEnforcedAtLeastN(
          [...assignments, ...nonDeathTargets],
          source.targetCountWhenAvailable,
          this.available.get(source) as BoolLike,
        );
      }
    }
  }
}
