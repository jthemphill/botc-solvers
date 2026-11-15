import { type Claim, gainedAbilityClaim } from "../schema/puzzleDoc";

/** A claim in the builder. A Philosopher claim gives the time of its choice to the claim about the gained ability. */
export type BuildClaim = Claim & { readonly gainedByPhilosopher?: { readonly timing?: string } };

/**
 * Puts the claim about a gained ability after its Philosopher claim, as a claim of its own.
 * The builder reads its reports and does not read it as a claim of a starting character.
 */
export function expandPhilosopherClaims(claims: readonly Claim[]): readonly BuildClaim[] {
  return claims.flatMap((claim): BuildClaim[] => {
    const gained = claim.type === "Philosopher" ? gainedAbilityClaim(claim) : undefined;
    if (claim.type !== "Philosopher" || gained === undefined) return [claim];
    return [
      { ...claim, gained: undefined },
      // A report without a time uses the time of the Philosopher choice.
      { ...gained, timing: gained.timing ?? claim.timing, gainedByPhilosopher: { timing: claim.timing } },
    ];
  });
}
