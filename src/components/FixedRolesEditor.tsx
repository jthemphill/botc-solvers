import type { Dispatch } from "react";
import type { FixedRoleConstraint, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function FixedRolesEditor({ doc, dispatch }: Props) {
  const fixedRoles = doc.fixedRoles ?? [];

  const setFixedRoles = (next: readonly FixedRoleConstraint[]) => {
    dispatch({ type: "setFixedRoles", fixedRoles: next.length === 0 ? undefined : next });
  };

  const updateFixedRole = (index: number, fixedRole: FixedRoleConstraint) => {
    setFixedRoles(fixedRoles.map((existing, i) => (i === index ? fixedRole : existing)));
  };

  const addFixedRole = () => {
    setFixedRoles([
      ...fixedRoles,
      {
        name: doc.players[0] ?? "",
        roles: doc.script[0] === undefined ? [] : [doc.script[0]],
      },
    ]);
  };

  const removeFixedRole = (index: number) => {
    setFixedRoles(fixedRoles.filter((_, i) => i !== index));
  };

  const toggleRole = (fixedRole: FixedRoleConstraint, role: string, checked: boolean): FixedRoleConstraint => ({
    ...fixedRole,
    roles: checked ? [...fixedRole.roles, role] : fixedRole.roles.filter((existing) => existing !== role),
  });

  return (
    <section className="panel">
      <h3>Fixed roles (optional)</h3>
      {fixedRoles.map((fixedRole, index) => {
        const selected = new Set(fixedRole.roles);
        return (
          <div key={index} className="claim-block">
            <header>
              <strong>Constraint {index + 1}</strong>
              <button onClick={() => removeFixedRole(index)}>Remove</button>
            </header>
            <div className="field-grid">
              <span>Player</span>
              <select
                value={fixedRole.name}
                onChange={(e) => updateFixedRole(index, { ...fixedRole, name: e.target.value })}
              >
                <option value="">-</option>
                {doc.players.map((player) => (
                  <option key={player} value={player}>
                    {player}
                  </option>
                ))}
              </select>
              <span>Possible roles</span>
              <div className="script-grid">
                {doc.script.map((role) => (
                  <label key={role}>
                    <input
                      type="checkbox"
                      checked={selected.has(role)}
                      onChange={(e) => updateFixedRole(index, toggleRole(fixedRole, role, e.target.checked))}
                    />
                    {role}
                  </label>
                ))}
              </div>
            </div>
          </div>
        );
      })}
      <button onClick={addFixedRole} disabled={doc.players.length === 0 || doc.script.length === 0}>
        + Add fixed role
      </button>
    </section>
  );
}
