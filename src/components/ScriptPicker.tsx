import { useMemo, useState, type Dispatch, type KeyboardEvent } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji } from "../model/roleEmoji";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { canonicalRoleName, hiddenScriptRoleOptions, protectedScriptRoles } from "../state/scriptRoles";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

const TYPE_LABEL: Record<CharacterType, string> = {
  [CharacterType.Townsfolk]: "Townsfolk",
  [CharacterType.Outsider]: "Outsider",
  [CharacterType.Minion]: "Minion",
  [CharacterType.Demon]: "Demon",
};

export function ScriptPicker({ doc, dispatch }: Props) {
  const [search, setSearch] = useState("");
  const selected = new Set(doc.script);
  const protectedRoles = new Set(protectedScriptRoles(doc));
  const hiddenRoles = useMemo(() => hiddenScriptRoleOptions(), []);
  const hiddenRoleSet = useMemo(() => new Set(hiddenRoles), [hiddenRoles]);
  const query = search.trim();
  const normalizedQuery = query.toLowerCase();
  const selectedHiddenRoles = hiddenRoles.filter((name) => selected.has(name));
  const matchingRoles =
    normalizedQuery === ""
      ? []
      : hiddenRoles.filter((name) => !selected.has(name) && name.toLowerCase().includes(normalizedQuery)).slice(0, 8);
  const exactRole = canonicalRoleName(query);
  const addableRole =
    exactRole !== undefined && hiddenRoleSet.has(exactRole) && !selected.has(exactRole) ? exactRole : undefined;

  const setRole = (name: string, on: boolean) => {
    if (selected.has(name) === on) return;
    if (!on && protectedRoles.has(name)) return;
    const next = on ? [...doc.script, name] : doc.script.filter((n) => n !== name);
    dispatch({ type: "setScript", script: next });
  };

  const addRole = (name: string) => {
    setRole(name, true);
    setSearch("");
  };

  const addCurrentOrFirstMatch = () => {
    const role = addableRole ?? matchingRoles[0];
    if (role !== undefined) addRole(role);
  };

  const onSearchKeyDown = (event: KeyboardEvent<HTMLInputElement>) => {
    if (event.key !== "Enter") return;
    event.preventDefault();
    addCurrentOrFirstMatch();
  };

  return (
    <section className="panel script-picker-panel">
      <header className="panel-heading-row">
        <div>
          <h3>Script</h3>
          <span>{selectedHiddenRoles.length} hidden roles selected</span>
        </div>
      </header>

      <div className="hidden-role-search">
        <input
          type="text"
          list="hidden-role-options"
          value={search}
          onChange={(event) => setSearch(event.target.value)}
          onKeyDown={onSearchKeyDown}
          placeholder="Search hidden roles"
          aria-label="Search hidden roles"
        />
        <datalist id="hidden-role-options">
          {hiddenRoles
            .filter((name) => !selected.has(name))
            .map((name) => (
              <option key={name} value={name} />
            ))}
        </datalist>
        <button
          type="button"
          onClick={addCurrentOrFirstMatch}
          disabled={addableRole === undefined && matchingRoles.length === 0}
        >
          Add
        </button>
      </div>

      {matchingRoles.length > 0 && (
        <div className="hidden-role-results">
          {matchingRoles.map((name) => (
            <button key={name} type="button" className="hidden-role-result" onClick={() => addRole(name)}>
              <span aria-hidden="true">{roleEmoji(name)}</span>
              {name}
            </button>
          ))}
        </div>
      )}

      <div className="role-palette script-role-palette">
        {selectedHiddenRoles.map((name) => {
          const locked = protectedRoles.has(name);
          const type = ROLE_CLASSES.get(name)?.characterType;
          return (
            <button
              key={name}
              type="button"
              className={`role-stamp selected${locked ? " locked" : ""}`}
              onClick={() => setRole(name, false)}
              disabled={locked}
              title={locked ? "Used by a claim or fixed role" : `Remove ${name}`}
            >
              <span aria-hidden="true">{roleEmoji(name)}</span>
              <small>{name}</small>
              {type !== undefined && <em>{TYPE_LABEL[type]}</em>}
            </button>
          );
        })}
        {selectedHiddenRoles.length === 0 && <p className="palette-empty">No hidden roles selected.</p>}
      </div>
    </section>
  );
}
