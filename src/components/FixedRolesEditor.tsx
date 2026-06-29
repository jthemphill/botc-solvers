import type { Dispatch } from "react";
import type { FixedRoleConstraint, ForbiddenRoleConstraint, PuzzleConstraintDoc, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { RoleListEditor, sortedRoleNames } from "./RolePicker";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function FixedRolesEditor({ doc, dispatch }: Props) {
  const fixedRoles = doc.fixedRoles ?? [];
  const forbiddenRoles = doc.forbiddenRoles ?? [];
  const customConstraints = doc.constraints ?? [];

  const setFixedRoles = (next: readonly FixedRoleConstraint[]) => {
    dispatch({ type: "setFixedRoles", fixedRoles: next.length === 0 ? undefined : next });
  };

  const setForbiddenRoles = (next: readonly ForbiddenRoleConstraint[]) => {
    dispatch({ type: "setForbiddenRoles", forbiddenRoles: next.length === 0 ? undefined : next });
  };

  const setCustomConstraints = (next: readonly PuzzleConstraintDoc[]) => {
    dispatch({ type: "setConstraints", constraints: next.length === 0 ? undefined : next });
  };

  return (
    <section className="panel">
      <h3>Role constraints (optional)</h3>
      <RoleConstraintList
        doc={doc}
        constraints={fixedRoles}
        roleLabel="Possible roles"
        addLabel="+ Add fixed role"
        emptyRole={[]}
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
      <CustomConstraintList constraints={customConstraints} setConstraints={setCustomConstraints} />
    </section>
  );
}

function CustomConstraintList({
  constraints,
  setConstraints,
}: {
  constraints: readonly PuzzleConstraintDoc[];
  setConstraints: (next: readonly PuzzleConstraintDoc[]) => void;
}) {
  const updateConstraint = (index: number, expression: string) => {
    setConstraints(constraints.map((constraint, i) => (i === index ? { ...constraint, expression } : constraint)));
  };

  const addConstraint = () => {
    setConstraints([...constraints, { expression: "" }]);
  };

  const removeConstraint = (index: number) => {
    setConstraints(constraints.filter((_, i) => i !== index));
  };

  return (
    <>
      {constraints.map((constraint, index) => (
        <div key={`custom-constraint-${index}`} className="claim-block">
          <header>
            <strong>Custom constraint {index + 1}</strong>
            <button type="button" onClick={() => removeConstraint(index)}>
              Remove
            </button>
          </header>
          <div className="field-grid">
            <span>Expression</span>
            <textarea value={constraint.expression} onChange={(event) => updateConstraint(index, event.target.value)} />
          </div>
        </div>
      ))}
      <button type="button" onClick={addConstraint}>
        + Add custom constraint
      </button>
    </>
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

  return (
    <>
      {constraints.map((fixedRole, index) => {
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
              <RoleListEditor
                value={fixedRole.roles}
                onChange={(roles) => updateFixedRole(index, { ...fixedRole, roles })}
                options={sortedRoleNames(doc.script)}
                label={roleLabel}
              />
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
