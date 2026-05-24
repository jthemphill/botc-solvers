import type { Dispatch } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { protectedScriptRoles } from "../state/scriptRoles";

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
  const selected = new Set(doc.script);
  const protectedRoles = new Set(protectedScriptRoles(doc));

  const groups: Record<CharacterType, string[]> = {
    [CharacterType.Townsfolk]: [],
    [CharacterType.Outsider]: [],
    [CharacterType.Minion]: [],
    [CharacterType.Demon]: [],
  };
  for (const [name, cls] of ROLE_CLASSES) groups[cls.characterType].push(name);
  for (const list of Object.values(groups)) list.sort();

  const toggle = (name: string, on: boolean) => {
    if (!on && protectedRoles.has(name)) return;
    const next = on ? [...doc.script, name] : doc.script.filter((n) => n !== name);
    dispatch({ type: "setScript", script: next });
  };

  const hiddenGroups: CharacterType[] = [CharacterType.Demon, CharacterType.Minion, CharacterType.Outsider];

  return (
    <section className="panel">
      <h3>Script</h3>
      <details open>
        <summary>Hidden roles</summary>
        <div className="hidden-role-groups">
          {hiddenGroups.map((type) => (
            <div key={type}>
              <strong>{TYPE_LABEL[type]}</strong>
              <div className="script-grid compact">
                {groups[type].map((name) => (
                  <RoleCheckbox
                    key={name}
                    name={name}
                    selected={selected.has(name)}
                    protectedRole={protectedRoles.has(name)}
                    onToggle={toggle}
                  />
                ))}
              </div>
            </div>
          ))}
        </div>
      </details>
      {(Object.keys(groups) as CharacterType[]).map((t) => (
        <details key={t} open>
          <summary>{TYPE_LABEL[t]}</summary>
          <div className="script-grid">
            {groups[t].map((name) => (
              <RoleCheckbox
                key={name}
                name={name}
                selected={selected.has(name)}
                protectedRole={protectedRoles.has(name)}
                onToggle={toggle}
              />
            ))}
          </div>
        </details>
      ))}
    </section>
  );
}

function RoleCheckbox({
  name,
  selected,
  protectedRole,
  onToggle,
}: {
  name: string;
  selected: boolean;
  protectedRole: boolean;
  onToggle: (name: string, selected: boolean) => void;
}) {
  return (
    <label className={protectedRole ? "protected-role" : undefined}>
      <input
        type="checkbox"
        checked={selected}
        disabled={selected && protectedRole}
        onChange={(e) => onToggle(name, e.target.checked)}
      />
      {name}
    </label>
  );
}
