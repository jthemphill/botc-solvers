import type { BoolLike, BOTCModel, Timing } from "./model";

export enum Alignment {
  Good = "good",
  Evil = "evil",
}

export enum CharacterType {
  Townsfolk = "townsfolk",
  Outsider = "outsider",
  Minion = "minion",
  Demon = "demon",
}

export enum StatusEffect {
  Poisoned = "poisoned",
}

export interface WakeRule {
  wakes(game: BOTCModel, player: string, timing: Timing, name: string): BoolLike;
}

export interface RoleClass {
  readonly roleName: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
  readonly maxCopies?: number;
  readonly wake: WakeRule;
}

export interface RoleInstance {
  readonly name: string;
  readonly roleName: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
  readonly maxCopies?: number;
}

export type RoleRef = string | RoleClass | RoleInstance;

export interface Character {
  readonly name: string;
  readonly alignment: Alignment;
  readonly characterType: CharacterType;
}

export interface RoleClaim {
  readonly player: string;
  readonly apparentRole: RoleRef;
}

function hasRoleName(value: unknown): value is { readonly roleName: string } {
  return (
    (typeof value === "object" || typeof value === "function") &&
    value !== null &&
    typeof (value as { roleName?: unknown }).roleName === "string"
  );
}

function hasLegacyName(value: unknown): value is { readonly name: string } {
  return (
    (typeof value === "object" || typeof value === "function") &&
    value !== null &&
    typeof (value as { name?: unknown }).name === "string"
  );
}

export function roleName(role: RoleRef): string {
  if (typeof role === "string") return role;
  if (hasRoleName(role)) return role.roleName;
  if (hasLegacyName(role as unknown)) return (role as { readonly name: string }).name;
  throw new TypeError(`Expected a role name, Character, or role class.`);
}

export function roleAlignment(role: RoleRef): Alignment {
  const alignment = (role as { alignment?: unknown }).alignment;
  if (alignment === Alignment.Good || alignment === Alignment.Evil) return alignment;
  throw new TypeError(`Role does not expose Alignment metadata.`);
}

export function roleCharacterType(role: RoleRef): CharacterType {
  const characterType = (role as { characterType?: unknown }).characterType;
  if (
    characterType === CharacterType.Townsfolk ||
    characterType === CharacterType.Outsider ||
    characterType === CharacterType.Minion ||
    characterType === CharacterType.Demon
  ) {
    return characterType;
  }
  throw new TypeError(`Role does not expose CharacterType metadata.`);
}

export function roleMaxCopies(role: RoleRef): number {
  const maxCopies = (role as { maxCopies?: unknown }).maxCopies;
  if (Number.isInteger(maxCopies) && (maxCopies as number) > 0) return maxCopies as number;
  if (roleName(role) === "Village Idiot") return 3;
  return 1;
}

export function roleWakeRule(role: RoleRef): WakeRule {
  const wake = (role as { wake?: unknown }).wake;
  if (typeof wake === "object" && wake !== null && typeof (wake as { wakes?: unknown }).wakes === "function") {
    return wake as WakeRule;
  }
  throw new TypeError(`${roleName(role)} does not expose wake metadata.`);
}
