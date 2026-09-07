import { useEffect, useLayoutEffect, useRef, useState, type Dispatch, type ReactNode } from "react";
import { roleEmojiLabel } from "../model/roleEmoji";
import { SUPPORTED_CLAIM_TYPES, type PuzzleDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { canonicalRoleName, normalizeRoleName } from "../state/scriptRoles";
import { makeEmptyClaim } from "./ClaimsEditor";
import { claimSummary } from "./claimSummary";
import { RoleTypeahead, sortedRoleNames } from "./RolePicker";

const claimTypes = [...SUPPORTED_CLAIM_TYPES];
const roleOptions = sortedRoleNames(claimTypes.map((type) => canonicalRoleName(type) ?? type));
const claimTypeFor = (role: string) => claimTypes.find((type) => normalizeRoleName(type) === normalizeRoleName(role));

interface Props {
  compact?: boolean;
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
  selectedIndex: number;
  onSelect: (index: number) => void;
  renderDetails?: (index: number) => ReactNode;
}

export function RosterEditor({ doc, dispatch, selectedIndex, onSelect, compact = false, renderDetails }: Props) {
  const [pasteOpen, setPasteOpen] = useState(false);
  const [draft, setDraft] = useState("");
  const dialog = useRef<HTMLDialogElement>(null);
  const roster = useRef<HTMLElement>(null);
  const nextNameToFocus = useRef<number | undefined>(undefined);
  const canReplace = doc.claims.length === 0 && !doc.timeline?.length && !doc.constraints?.length;
  const rows = draft
    .split(/\n|,/)
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line) => {
      const [name = "", role = "", ...extra] = line.split(/\t|\s*=\s*/);
      return { name: name.trim(), role: role.trim(), extra, type: role.trim() ? claimTypeFor(role.trim()) : undefined };
    });
  const error = rows.some((row) => row.extra.length)
    ? "Use one name and one character per line. Add report details in the claim editor."
    : rows.some((row) => !row.name)
      ? "Each player needs a name."
      : new Set(rows.map((row) => row.name)).size !== rows.length
        ? "Use a different name for each player."
        : rows.some((row) => row.role && !row.type)
          ? "One of the characters is not supported. Check its spelling."
          : !canReplace && rows.some((row) => doc.players.includes(row.name))
            ? "These names are already in the roster. Edit their rows instead."
            : (canReplace ? rows.length : doc.players.length + rows.length) > 20
              ? "Use up to 20 players."
              : undefined;

  useEffect(() => {
    if (pasteOpen) {
      dialog.current?.showModal();
      dialog.current?.querySelector("textarea")?.focus();
    } else dialog.current?.close();
  }, [pasteOpen]);

  useLayoutEffect(() => {
    const index = nextNameToFocus.current;
    nextNameToFocus.current = undefined;
    if (index !== undefined) roster.current?.querySelectorAll<HTMLInputElement>(".roster-name")[index]?.focus();
  }, [doc.claims.length]);

  const applyRoster = () => {
    if (error || !rows.length) return;
    dispatch({
      type: "load",
      doc: {
        ...doc,
        players: [...(canReplace ? [] : doc.players), ...rows.map((row) => row.name)],
        claims: [...doc.claims, ...rows.flatMap((row) => (row.type ? [makeEmptyClaim(row.type, row.name)] : []))],
      },
    });
    onSelect(canReplace ? 0 : doc.players.length);
    setPasteOpen(false);
    setDraft("");
  };

  return (
    <section ref={roster} className={`roster-editor${compact ? " compact" : ""}`} aria-label="Player roster">
      <header className="section-heading">
        <div>
          <h2>Players & claims</h2>
          <p>Clockwise from seat 1. Select a report to edit its details.</p>
        </div>
        <button type="button" onClick={() => setPasteOpen(true)}>
          Paste roster
        </button>
      </header>
      <div className="roster-columns" aria-hidden="true">
        <span>Seat</span>
        <span>Player</span>
        <span>Claimed character / report</span>
      </div>
      <div className="roster-rows">
        {doc.players.map((name, index) => {
          const claims = doc.claims.filter((claim) => claim.name === name);
          return (
            <div className={`roster-row${selectedIndex === index ? " selected" : ""}`} key={index}>
              <span className="roster-seat">{String(index + 1).padStart(2, "0")}</span>
              <PlayerName
                name={name}
                index={index}
                players={doc.players}
                onChange={(next) => dispatch({ type: "renamePlayer", index, name: next })}
              />
              <div className="roster-reports">
                {claims.length === 0 ? (
                  <RoleTypeahead
                    value=""
                    options={roleOptions}
                    allowEmpty
                    ariaLabel={`Claim for ${name}`}
                    placeholder="Choose a character…"
                    onChange={(role) => {
                      const type = claimTypeFor(role);
                      if (!role || !type) return;
                      if (!renderDetails) nextNameToFocus.current = index + 1;
                      dispatch({ type: "addClaim", claim: makeEmptyClaim(type, name) });
                      onSelect(index);
                    }}
                  />
                ) : (
                  <button
                    className="roster-report"
                    type="button"
                    aria-label={`Edit claims for ${name}`}
                    aria-pressed={selectedIndex === index}
                    onClick={() => {
                      onSelect(index);
                      if (!renderDetails && window.matchMedia("(max-width: 900px)").matches)
                        document.getElementById("claims-panel")?.scrollIntoView({ behavior: "smooth", block: "start" });
                    }}
                  >
                    <strong>{[...new Set(claims.map((claim) => roleEmojiLabel(claim.type)))].join(" · ")}</strong>
                    <span>{claims.map((claim) => claimSummary(claim)).join(" · ")}</span>
                    {claims.length > 1 && <small>{claims.length} reports</small>}
                  </button>
                )}
              </div>
              {renderDetails?.(index)}
            </div>
          );
        })}
      </div>
      <footer className="roster-footer">
        <button
          type="button"
          disabled={doc.players.length >= 20}
          onClick={() => dispatch({ type: "setPlayerCount", count: doc.players.length + 1 })}
        >
          + Add player
        </button>
        <span>Tab between names and characters · Enter to choose</span>
      </footer>
      <dialog
        ref={dialog}
        className="roster-dialog"
        onCancel={() => setPasteOpen(false)}
        onClose={() => setPasteOpen(false)}
      >
        <form
          onSubmit={(event) => {
            event.preventDefault();
            applyRoster();
          }}
        >
          <header className="section-heading">
            <div>
              <h2>Paste your roster</h2>
              <p>Names in clockwise order. Add a claimed character with = or a tab.</p>
            </div>
            <button type="button" aria-label="Close roster entry" onClick={() => setPasteOpen(false)}>
              ×
            </button>
          </header>
          <label htmlFor="roster-paste">Players and claimed characters</label>
          <textarea
            id="roster-paste"
            autoFocus
            value={draft}
            onChange={(event) => setDraft(event.target.value)}
            placeholder={"Anna = Empath\nTim = Fortune Teller\nSula = Steward"}
            onKeyDown={(event) => {
              if (event.key === "Enter" && (event.metaKey || event.ctrlKey)) {
                event.preventDefault();
                applyRoster();
              }
            }}
          />
          <p className="roster-paste-help">
            You can also paste comma-separated names or two columns from a spreadsheet.{" "}
            {canReplace ? "This sets the seating order." : "New players will be added after the last seat."}
          </p>
          <p role="status" className={error ? "error" : "roster-preview"}>
            {error ?? `${rows.length} players · ${rows.filter((row) => row.type).length} claims`}
          </p>
          <footer>
            <span>⌘ / Ctrl + Enter to apply</span>
            <button className="primary-button" type="submit" disabled={!!error || !rows.length}>
              Use roster
            </button>
          </footer>
        </form>
      </dialog>
    </section>
  );
}

export function PlayerName({
  name,
  index,
  players,
  onChange,
  ariaLabel,
}: {
  name: string;
  index: number;
  players: readonly string[];
  onChange: (name: string) => void;
  ariaLabel?: string;
}) {
  const [draft, setDraft] = useState(name);
  useEffect(() => setDraft(name), [name]);
  const invalid = !draft.trim() || (draft.trim() !== name && players.includes(draft.trim()));
  const commit = () => {
    if (!invalid) onChange(draft.trim());
    else setDraft(name);
  };
  return (
    <input
      className="roster-name"
      type="text"
      aria-label={ariaLabel ?? `Player ${index + 1} name`}
      value={draft}
      aria-invalid={invalid}
      title={invalid ? "Use a unique, nonempty name." : undefined}
      onChange={(event) => setDraft(event.target.value)}
      onFocus={(event) => event.currentTarget.select()}
      onBlur={commit}
      onKeyDown={(event) => {
        if (event.key === "Enter") {
          event.preventDefault();
          commit();
          event.currentTarget.closest(".roster-row")?.querySelector<HTMLInputElement>(".roster-reports input")?.focus();
        }
        if (event.key === "Escape") setDraft(name);
      }}
    />
  );
}
