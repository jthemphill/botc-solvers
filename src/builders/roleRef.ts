import type { RoleClass } from "../model/core";
import { roleByName } from "../model/roleRegistry";

export function resolveRoleRef(name: string): RoleClass {
  return roleByName(name);
}
