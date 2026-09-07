import { useEffect, useMemo, useRef, useState, type Dispatch } from "react";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji } from "../model/roleEmoji";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { ALL_ROLE_NAMES, canonicalRoleName, protectedScriptRoles } from "../state/scriptRoles";
import { RoleTypeahead, sortedRoleNames } from "./RolePicker";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function claimedRoles(doc: PuzzleDoc): string[] {
  return sortedRoleNames(
    doc.claims.flatMap((claim) => {
      const role = canonicalRoleName(claim.type);
      return role === undefined ? [] : [role];
    }),
  );
}

export function hiddenRoles(doc: PuzzleDoc): string[] {
  const publicRoles = new Set(claimedRoles(doc));
  return sortedRoleNames(doc.script.filter((role) => !publicRoles.has(role)));
}

export function HiddenRolesEditor({ doc, dispatch }: Props) {
  const [addKey, setAddKey] = useState(0);
  const [pickerOpen, setPickerOpen] = useState(false);
  const [query, setQuery] = useState("");
  const [category, setCategory] = useState("");
  const dialog = useRef<HTMLDialogElement>(null);
  useEffect(() => {
    if (pickerOpen) dialog.current?.showModal();
    else dialog.current?.close();
  }, [pickerOpen]);
  const publicRoles = useMemo(() => claimedRoles(doc), [doc]);
  const publicRoleSet = useMemo(() => new Set(publicRoles), [publicRoles]);
  const roles = useMemo(() => hiddenRoles(doc), [doc]);
  const roleSet = useMemo(() => new Set(roles), [roles]);
  const lockedRoleSet = useMemo(
    () => new Set(protectedScriptRoles(doc).filter((role) => !publicRoleSet.has(role))),
    [doc, publicRoleSet],
  );
  const availableRoles = useMemo(
    () => ALL_ROLE_NAMES.filter((role) => !publicRoleSet.has(role) && !roleSet.has(role)),
    [publicRoleSet, roleSet],
  );

  const addRole = (role: string) => {
    if (!role || roleSet.has(role) || publicRoleSet.has(role)) return;
    dispatch({ type: "setScript", script: [...doc.script, role] });
    setAddKey((key) => key + 1);
  };

  const removeRole = (role: string) => {
    if (lockedRoleSet.has(role)) return;
    dispatch({ type: "setScript", script: doc.script.filter((entry) => entry !== role) });
  };

  return (
    <section id="hidden-roles" className="panel hidden-roles-editor">
      <header className="panel-heading-row">
        <div>
          <h3>Potential hidden roles</h3>
          <span>Claimed roles are included automatically.</span>
        </div>
        <span className="panel-count">{roles.length}</span>
      </header>

      <div className="hidden-role-chips" aria-label="Potential hidden roles">
        {roles.map((role) => {
          const locked = lockedRoleSet.has(role);
          const characterType = ROLE_CLASSES.get(role)?.characterType;
          return (
            <button
              key={role}
              type="button"
              className={`hidden-role-chip${locked ? " locked" : ""}`}
              onClick={() => removeRole(role)}
              disabled={locked}
              title={locked ? "Used by claim details or a custom constraint" : `Remove ${role}`}
            >
              <span aria-hidden="true">{roleEmoji(role) ?? "?"}</span>
              <span>{role}</span>
              {characterType !== undefined && <small>{characterType}</small>}
              {!locked && <span aria-hidden="true">×</span>}
            </button>
          );
        })}
        {roles.length === 0 && <p className="palette-empty">No hidden roles selected.</p>}
      </div>

      <label className="hidden-role-add">
        <span>Add hidden role</span>
        <RoleTypeahead
          key={addKey}
          value=""
          onChange={addRole}
          options={availableRoles}
          allowEmpty
          ariaLabel="Add hidden role"
          placeholder="Search roles"
        />
      </label>
      <button className="choose-hidden-roles" type="button" onClick={() => setPickerOpen(true)}>
        Choose hidden roles
      </button>
      <dialog
        className="hidden-roles-dialog"
        ref={dialog}
        aria-label="Choose hidden roles"
        onCancel={() => setPickerOpen(false)}
        onClose={() => setPickerOpen(false)}
      >
        <header>
          <div>
            <h2>Hidden roles</h2>
            <p>Choose every character that could be in play.</p>
          </div>
          <button type="button" aria-label="Close hidden role picker" onClick={() => setPickerOpen(false)}>
            Done
          </button>
        </header>
        <input
          type="search"
          aria-label="Search hidden roles"
          placeholder="Search all characters…"
          value={query}
          onChange={(event) => setQuery(event.target.value)}
        />
        <div className="hidden-role-categories" aria-label="Character types">
          {[
            ["", "All"],
            ["outsider", "Outsiders"],
            ["minion", "Minions"],
            ["demon", "Demons"],
            ["townsfolk", "Townsfolk"],
          ].map(([value, label]) => (
            <button
              type="button"
              key={value}
              aria-pressed={category === value && !query}
              onClick={() => {
                setCategory(value!);
                setQuery("");
              }}
            >
              {label}
            </button>
          ))}
        </div>
        <div className="hidden-role-options">
          {sortedRoleNames(ALL_ROLE_NAMES)
            .filter(
              (role) =>
                !publicRoleSet.has(role) &&
                (query
                  ? role.toLowerCase().includes(query.toLowerCase())
                  : !category || ROLE_CLASSES.get(role)?.characterType === category),
            )
            .map((role) => (
              <label key={role} className={roleSet.has(role) ? "chosen" : ""}>
                <input
                  type="checkbox"
                  aria-label={role}
                  checked={roleSet.has(role)}
                  disabled={lockedRoleSet.has(role)}
                  onChange={(event) => (event.target.checked ? addRole(role) : removeRole(role))}
                />
                <span>
                  {roleEmoji(role)} {role}
                </span>
                {lockedRoleSet.has(role) && <small>Used in a report</small>}
              </label>
            ))}
        </div>
        <footer>{roles.length} hidden roles selected · claimed roles are included automatically.</footer>
      </dialog>
    </section>
  );
}
