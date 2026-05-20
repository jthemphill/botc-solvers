import { type RoleRef, roleName } from "./core";
import type { World } from "./model";

export interface ForcedRole {
  readonly label: string;
  readonly roles: readonly string[];
  readonly missing: string;
  readonly includeRole: boolean;
}

export type ForcedRoleSpec = RoleRef | ForcedRole;

export function forcedRole(
  label: RoleRef,
  roles?: RoleRef | readonly RoleRef[],
  options: { readonly missing?: string; readonly includeRole?: boolean } = {},
): ForcedRole {
  const labelName = roleName(label);
  let roleNames: string[];
  if (roles === undefined) roleNames = [labelName];
  else if (Array.isArray(roles)) roleNames = (roles as readonly RoleRef[]).map((role) => roleName(role));
  else roleNames = [roleName(roles as RoleRef)];
  if (roleNames.length === 0) throw new Error("At least one role is required.");
  return {
    label: labelName,
    roles: roleNames,
    missing: options.missing ?? "not forced",
    includeRole: options.includeRole ?? false,
  };
}

export function formatSolution(
  worlds: readonly World[],
  players: readonly string[],
  options: {
    readonly forcedRoles?: readonly ForcedRoleSpec[];
    readonly forcedMissing?: string;
    readonly poisonContext?: string;
  } = {},
): string {
  const facts = (options.forcedRoles ?? []).map((role) =>
    coerceForcedRole(role, options.forcedMissing ?? "not forced"),
  );
  const lines = [`${worlds.length} satisfying world(s)`];
  worlds.forEach((world, index) => {
    lines.push("", `World ${index + 1}`, ...formatWorldLines(world, players, options.poisonContext));
  });
  if (facts.length > 0) {
    lines.push("", "Forced facts");
    for (const fact of facts) lines.push(`  ${formatForcedRole(worlds, fact)}`);
  }
  return lines.join("\n");
}

export function printSolution(
  worlds: readonly World[],
  players: readonly string[],
  options: {
    readonly forcedRoles?: readonly ForcedRoleSpec[];
    readonly forcedMissing?: string;
    readonly poisonContext?: string;
  } = {},
): void {
  console.log(formatSolution(worlds, players, options));
}

function coerceForcedRole(role: ForcedRoleSpec, forcedMissing: string): ForcedRole {
  if (typeof role === "object" && role !== null && "roles" in role && "label" in role) return role as ForcedRole;
  return forcedRole(role as RoleRef, undefined, { missing: forcedMissing });
}

function formatWorldLines(world: World, players: readonly string[], poisonContext?: string): string[] {
  return players.map((player) => {
    const actual = world.actualRole(player);
    const apparent = world.apparent.get(player);
    const poisonSuffix = world.isPoisoned(player, poisonContext) ? " poisoned" : "";
    return apparent !== undefined && apparent !== actual
      ? `  ${player}: ${actual} (appears as ${apparent})${poisonSuffix}`
      : `  ${player}: ${actual}${poisonSuffix}`;
  });
}

function formatForcedRole(worlds: readonly World[], role: ForcedRole): string {
  const assignment = forcedAssignment(worlds, role);
  if (assignment === undefined) return `${role.label}: ${role.missing}`;
  const [holder, actualRole] = assignment;
  return role.includeRole ? `${role.label}: ${holder} (${actualRole})` : `${role.label}: ${holder}`;
}

function forcedAssignment(worlds: readonly World[], role: ForcedRole): readonly [string, string] | undefined {
  const assignments = new Map<string, readonly [string, string] | undefined>();
  for (const world of worlds) {
    const assignment = worldAssignment(world, role.roles);
    assignments.set(role.includeRole ? JSON.stringify(assignment) : JSON.stringify(assignment?.[0]), assignment);
  }
  return assignments.size === 1 ? [...assignments.values()][0] : undefined;
}

function worldAssignment(world: World, roles: readonly string[]): readonly [string, string] | undefined {
  const assignments = roles.flatMap((role) => {
    const holder = world.holder(role);
    return holder === undefined ? [] : [[holder, role] as const];
  });
  return assignments.length === 1 ? assignments[0] : undefined;
}
