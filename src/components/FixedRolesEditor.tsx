import type { Dispatch } from "react";
import type { FixedRoleConstraint, ForbiddenRoleConstraint, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function FixedRolesEditor({ doc, dispatch }: Props) {
  const fixedRoles = doc.fixedRoles ?? [];
  const forbiddenRoles = doc.forbiddenRoles ?? [];

  const setFixedRoles = (next: readonly FixedRoleConstraint[]) => {
    dispatch({ type: "setFixedRoles", fixedRoles: next.length === 0 ? undefined : next });
  };

  const setForbiddenRoles = (next: readonly ForbiddenRoleConstraint[]) => {
    dispatch({ type: "setForbiddenRoles", forbiddenRoles: next.length === 0 ? undefined : next });
  };

  return (
    <section className="panel">
      <h3>Role constraints (optional)</h3>
      <RoleConstraintList
        doc={doc}
        constraints={fixedRoles}
        roleLabel="Possible roles"
        addLabel="+ Add fixed role"
        emptyRole={doc.script[0] === undefined ? [] : [doc.script[0]]}
        setConstraints={setFixedRoles}
      />
      <RoleConstraintList
        doc={doc}
        constraints={forbiddenRoles}
        roleLabel="Excluded roles"
        addLabel="+ Add excluded role"
        emptyRole={[]}
        setConstraints={setForbiddenRoles}
      />
    </section>
  );
}

function RoleConstraintList<T extends FixedRoleConstraint | ForbiddenRoleConstraint>({
  doc,
  constraints,
  roleLabel,
  addLabel,
  emptyRole,
  setConstraints,
}: {
  doc: PuzzleDoc;
  constraints: readonly T[];
  roleLabel: string;
  addLabel: string;
  emptyRole: readonly string[];
  setConstraints: (next: readonly T[]) => void;
}) {
  const updateFixedRole = (index: number, fixedRole: FixedRoleConstraint) => {
    setConstraints(constraints.map((existing, i) => (i === index ? (fixedRole as T) : existing)));
  };

  const addFixedRole = () => {
    setConstraints([
      ...constraints,
      {
        name: doc.players[0] ?? "",
        roles: emptyRole,
      } as T,
    ]);
  };

  const removeFixedRole = (index: number) => {
    setConstraints(constraints.filter((_, i) => i !== index));
  };

  const toggleRole = (fixedRole: FixedRoleConstraint, role: string, checked: boolean): FixedRoleConstraint => ({
    ...fixedRole,
    roles: checked ? [...fixedRole.roles, role] : fixedRole.roles.filter((existing) => existing !== role),
  });

  return (
    <>
      {constraints.map((fixedRole, index) => {
        const selected = new Set(fixedRole.roles);
        return (
          <div key={`${roleLabel}-${index}`} className="claim-block">
            <header>
              <strong>
                {roleLabel} constraint {index + 1}
              </strong>
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
              <span>{roleLabel}</span>
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
        {addLabel}
      </button>
    </>
  );
}
