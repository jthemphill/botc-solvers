import styles from "./ConstraintsEditor.module.css";
import type { Dispatch } from "react";
import type { PuzzleConstraintDoc, PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export function ConstraintsEditor({ doc, dispatch }: Props) {
  const customConstraints = doc.constraints ?? [];

  const setCustomConstraints = (next: readonly PuzzleConstraintDoc[]) => {
    dispatch({ type: "setConstraints", constraints: next.length === 0 ? undefined : next });
  };

  return (
    <section className={`${styles.root} panel constraints-editor`}>
      <h3>Custom constraints</h3>
      <CustomConstraintList constraints={customConstraints} setConstraints={setCustomConstraints} />
      <details className="advanced-puzzle-rules">
        <summary>Advanced puzzle rules</summary>
        <p>
          Most puzzles can use the inferred defaults. Change these only when the published rules explicitly require it.
        </p>
        <label className="checkbox-row">
          <input
            type="checkbox"
            aria-label="Use standard setup counts"
            checked={doc.setup !== "none" && doc.setup !== "atheist"}
            onChange={(event) => dispatch({ type: "setSetup", setup: event.target.checked ? undefined : "none" })}
          />
          <span>Use standard setup counts</span>
        </label>
        <label className="checkbox-row">
          <input
            type="checkbox"
            aria-label="Atheist puzzle rules"
            checked={doc.setup === "atheist"}
            onChange={(event) => dispatch({ type: "setSetup", setup: event.target.checked ? "atheist" : undefined })}
          />
          <span>Atheist puzzle rules</span>
        </label>
        <label className="checkbox-row">
          <input
            type="checkbox"
            aria-label="Unique actual characters"
            checked={doc.uniqueCharacters !== false}
            onChange={(event) =>
              dispatch({
                type: "setUniqueCharacters",
                uniqueCharacters: event.target.checked ? undefined : false,
              })
            }
          />
          <span>Unique actual characters</span>
        </label>
        <label className="checkbox-row">
          <input
            type="checkbox"
            aria-label="Abilities never target dead players to kill"
            checked={doc.noKillSinking === true}
            onChange={(event) =>
              dispatch({ type: "setNoKillSinking", noKillSinking: event.target.checked ? true : undefined })
            }
          />
          <span>Abilities never target dead players to kill</span>
        </label>
      </details>
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
  const updateConstraint = (index: number, change: Partial<PuzzleConstraintDoc>) => {
    setConstraints(constraints.map((constraint, i) => (i === index ? { ...constraint, ...change } : constraint)));
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
            <textarea
              aria-label={`Custom constraint ${index + 1} expression`}
              value={constraint.expression}
              onChange={(event) => updateConstraint(index, { expression: event.target.value })}
            />
            <span>Source</span>
            <input
              aria-label={`Custom constraint ${index + 1} source`}
              value={constraint.source ?? ""}
              onChange={(event) => updateConstraint(index, { source: event.target.value || undefined })}
            />
            <span>Kind</span>
            <select
              aria-label={`Custom constraint ${index + 1} kind`}
              value={constraint.kind ?? ""}
              onChange={(event) =>
                updateConstraint(index, { kind: (event.target.value || undefined) as PuzzleConstraintDoc["kind"] })
              }
            >
              <option value="">-</option>
              <option value="fact">fact</option>
              <option value="assumption">assumption</option>
            </select>
          </div>
        </div>
      ))}
      <button type="button" onClick={addConstraint}>
        + Add custom constraint
      </button>
    </>
  );
}
