import { useMemo, useState, type Dispatch, type KeyboardEvent } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji } from "../model/roleEmoji";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { ALL_ROLE_NAMES, canonicalRoleName, protectedScriptRoles } from "../state/scriptRoles";

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
  const roleOptions = useMemo(() => ALL_ROLE_NAMES, []);
  const roleOptionSet = useMemo(() => new Set(roleOptions), [roleOptions]);
  const query = search.trim();
  const normalizedQuery = query.toLowerCase();
  const selectedRoles = roleOptions.filter((name) => selected.has(name));
  const matchingRoles =
    normalizedQuery === ""
      ? []
      : roleOptions.filter((name) => !selected.has(name) && name.toLowerCase().includes(normalizedQuery)).slice(0, 8);
  const exactRole = canonicalRoleName(query);
  const addableRole =
    exactRole !== undefined && roleOptionSet.has(exactRole) && !selected.has(exactRole) ? exactRole : undefined;

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
          <span>{selectedRoles.length} roles selected</span>
        </div>
      </header>

      <div className="script-rules-grid">
        <label>
          <span>Setup</span>
          <select
            value={doc.setup ?? "standard"}
            onChange={(event) =>
              dispatch({
                type: "setSetup",
                setup: event.target.value === "standard" ? undefined : (event.target.value as PuzzleDoc["setup"]),
              })
            }
          >
            <option value="standard">Standard</option>
            <option value="none">No setup</option>
            <option value="atheist">Atheist</option>
          </select>
        </label>
        <label className="checkbox-row">
          <input
            type="checkbox"
            checked={doc.uniqueCharacters !== false}
            onChange={(event) =>
              dispatch({
                type: "setUniqueCharacters",
                uniqueCharacters: event.target.checked ? undefined : false,
              })
            }
          />
          <span>Unique characters</span>
        </label>
      </div>

      <div className="hidden-role-search">
        <input
          type="text"
          list="role-options"
          value={search}
          onChange={(event) => setSearch(event.target.value)}
          onKeyDown={onSearchKeyDown}
          placeholder="Search roles"
          aria-label="Search roles"
        />
        <datalist id="role-options">
          {roleOptions
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
        {selectedRoles.map((name) => {
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
        {selectedRoles.length === 0 && <p className="palette-empty">No roles selected.</p>}
      </div>
    </section>
  );
}
