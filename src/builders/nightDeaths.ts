import { type BooleanConstraints, type BoolLike, type BoolVar } from "../model/boolean";
import { addMapValue } from "../model/keys";

export interface NightDeathSource {
  readonly id: string;
  readonly available: BoolLike;
  readonly players?: readonly string[];
  readonly maxAssignments?: number;
  readonly targetCountWhenAvailable?: number;
  readonly requiredWhenAvailable?: boolean;
  readonly kind?: "demon" | "po";
  /** The Demon characters that can use this source. */
  readonly roles?: readonly string[];
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
    private readonly players: readonly string[],
    private readonly deadAtStart: ReadonlySet<string>,
    private readonly noKillSinking = false,
  ) {}

  assign(player: string, source: NightDeathSource): BoolVar {
    const value = this.game.newBool();
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
    );
  }

  constrainSources(): void {
    const { game } = this;
    const sourceCapacityActive = game.constantBool(true);
    for (const [source, assignments] of this.bySource) {
      game.addEnforcedAtMostN(assignments, source.maxAssignments ?? 1, sourceCapacityActive);
      const sourceAssigned = assignments.length === 1 ? (assignments[0] as BoolLike) : game.anyOf(assignments);
      let effectiveAvailability = source.available;
      if (source.requiresAliveAtResolution !== undefined) {
        const actor = source.requiresAliveAtResolution;
        const aliveAtPhaseStart = game.constantBool(this.players.includes(actor) && !this.deadAtStart.has(actor));
        const diesEarlier = this.earlierDeath(actor, source);
        effectiveAvailability = game.allOf([source.available, aliveAtPhaseStart, game.not(diesEarlier)]);
        for (const assignment of assignments) game.addImplication(assignment, effectiveAvailability);
      }
      this.available.set(source, effectiveAvailability);
      if (source.requiredWhenAvailable !== false) game.addImplication(effectiveAvailability, sourceAssigned);
    }
  }

  constrainTargets(protectionAt: (player: string) => BoolLike): void {
    const { game } = this;
    const deadAtPhaseStart = this.deadAtStart;
    for (const [source, assignments] of this.bySource) {
      if (source.kind === undefined) continue;
      const nonDeathTargets = this.players.map((player) => {
        const killedBySource = game.anyOf(
          this.deaths.filter((death) => death.player === player && death.source === source).map((death) => death.value),
        );
        const diesEarlier = this.earlierDeath(player, source);
        const survivesDemonTarget = game.anyOf([
          game.constantBool(deadAtPhaseStart.has(player)),
          diesEarlier,
          protectionAt(player),
        ]);
        return game.allOf([
          survivesDemonTarget,
          ...(this.noKillSinking ? [game.constantBool(!deadAtPhaseStart.has(player)), game.not(diesEarlier)] : []),
          game.not(killedBySource),
        ]);
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
