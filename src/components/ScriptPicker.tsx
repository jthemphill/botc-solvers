import type { Dispatch } from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import type { PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

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

  const groups: Record<CharacterType, string[]> = {
    [CharacterType.Townsfolk]: [],
    [CharacterType.Outsider]: [],
    [CharacterType.Minion]: [],
    [CharacterType.Demon]: [],
  };
  for (const [name, cls] of ROLE_CLASSES) groups[cls.characterType].push(name);
  for (const list of Object.values(groups)) list.sort();

  const toggle = (name: string, on: boolean) => {
    const next = on ? [...doc.script, name] : doc.script.filter((n) => n !== name);
    dispatch({ type: "setScript", script: next });
  };

  return (
    <section className="panel">
      <h3>Script</h3>
      {(Object.keys(groups) as CharacterType[]).map((t) => (
        <details key={t} open>
          <summary>{TYPE_LABEL[t]}</summary>
          <div className="script-grid">
            {groups[t].map((name) => (
              <label key={name}>
                <input type="checkbox" checked={selected.has(name)} onChange={(e) => toggle(name, e.target.checked)} />
                {name}
              </label>
            ))}
          </div>
        </details>
      ))}
    </section>
  );
}
