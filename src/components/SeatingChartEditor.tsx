import {
  useEffect,
  useRef,
  useState,
  type CSSProperties,
  type Dispatch,
  type DragEvent,
  type KeyboardEvent,
  type PointerEvent,
} from "react";
import { CharacterType } from "../model/core";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { roleEmoji, roleEmojiLabel } from "../model/roleEmoji";
import { standardSetupCounts } from "../model/setup";
import type { Claim, PuzzleDoc, TimelineEventDoc } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { hiddenScriptRoleOptions } from "../state/scriptRoles";
import { CLAIM_TYPES, ClaimBody, makeEmptyClaim } from "./ClaimsEditor";
import { claimSummary, compactTimingLabel, formatList, timingLabel } from "./claimSummary";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

interface SharedProps extends Props {
  selectedIndex: number;
  onSelect: (index: number) => void;
}

interface DrawWorkbenchProps extends Props {
  selectedIndex: number;
}

interface ClaimQuoteCard {
  readonly player: string;
  readonly playerIndex: number;
  readonly claimIndex: number;
  readonly roleLabel: string;
  readonly summary: string;
}

const TYPE_LABEL: Record<CharacterType, string> = {
  [CharacterType.Townsfolk]: "Townsfolk",
  [CharacterType.Outsider]: "Outsider",
  [CharacterType.Minion]: "Minion",
  [CharacterType.Demon]: "Demon",
};

const SEAT_DRAG_TYPE = "application/x-botc-seat-index";
const DOUBLE_TAP_WINDOW_MS = 450;

export function SeatingChartEditor({ doc, dispatch }: Props) {
  const [selectedIndex, setSelectedIndex] = useState(0);
  return (
    <section className="seating-composer">
      <PuzzleSheet doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} onSelect={setSelectedIndex} />
      <DrawWorkbench doc={doc} dispatch={dispatch} selectedIndex={selectedIndex} />
    </section>
  );
}

export function PuzzleSheet({ doc, dispatch, selectedIndex, onSelect }: SharedProps) {
  const players = doc.players;
  const selectedName = players[selectedIndex];
  const setupCounts = countSetupRoles(doc);
  const hasTimeline = doc.timeline !== undefined && doc.timeline.length > 0;
  const [draggedIndex, setDraggedIndex] = useState<number | undefined>(undefined);
  const [editingIndex, setEditingIndex] = useState<number | undefined>(undefined);
  const [draftName, setDraftName] = useState("");
  const [trashDropActive, setTrashDropActive] = useState(false);
  const lastSeatTap = useRef<{ index: number; time: number }>({ index: -1, time: 0 });
  const quoteCards = claimQuoteCardsForDoc(doc);
  const chartQuoteCards = players.length <= 10 ? firstQuoteCardsByPlayer(quoteCards) : [];

  useEffect(() => {
    if (selectedIndex >= players.length) onSelect(Math.max(0, players.length - 1));
  }, [onSelect, players.length, selectedIndex]);

  useEffect(() => {
    if (editingIndex !== undefined && editingIndex >= players.length) {
      setEditingIndex(undefined);
      setDraftName("");
    }
  }, [editingIndex, players.length]);

  const beginRename = (index: number, name: string) => {
    setDraggedIndex(undefined);
    setTrashDropActive(false);
    onSelect(index);
    setEditingIndex(index);
    setDraftName(name);
  };

  const commitRename = () => {
    if (editingIndex === undefined) return;
    const currentName = players[editingIndex];
    const nextName = draftName.trim();
    if (currentName !== undefined && nextName !== currentName) {
      dispatch({ type: "renamePlayer", index: editingIndex, name: nextName });
    }
    setEditingIndex(undefined);
    setDraftName("");
  };

  const cancelRename = () => {
    setEditingIndex(undefined);
    setDraftName("");
  };

  const startSeatDrag = (event: DragEvent<HTMLDivElement>, index: number) => {
    if (editingIndex === index) {
      event.preventDefault();
      return;
    }
    setDraggedIndex(index);
    setTrashDropActive(false);
    event.dataTransfer.effectAllowed = "move";
    event.dataTransfer.setData(SEAT_DRAG_TYPE, String(index));
    event.dataTransfer.setData("text/plain", String(index));
  };

  const draggedSeatIndex = (event: DragEvent<HTMLElement>) => {
    const value = event.dataTransfer.getData(SEAT_DRAG_TYPE) || event.dataTransfer.getData("text/plain");
    if (value === "") return draggedIndex;
    const dataIndex = Number(value);
    return Number.isInteger(dataIndex) ? dataIndex : draggedIndex;
  };

  const allowSeatDrop = (event: DragEvent<HTMLElement>) => {
    event.preventDefault();
    event.dataTransfer.dropEffect = "move";
  };

  const dropSeat = (event: DragEvent<HTMLDivElement>, toIndex: number) => {
    event.preventDefault();
    const fromIndex = draggedSeatIndex(event);
    setDraggedIndex(undefined);
    setTrashDropActive(false);
    if (fromIndex === undefined || fromIndex === toIndex || fromIndex < 0 || fromIndex >= players.length) return;
    dispatch({ type: "movePlayerTo", fromIndex, toIndex });
    onSelect(toIndex);
  };

  const dropSeatOnTrash = (event: DragEvent<HTMLDivElement>) => {
    event.preventDefault();
    const fromIndex = draggedSeatIndex(event);
    setDraggedIndex(undefined);
    setTrashDropActive(false);
    if (fromIndex === undefined || fromIndex < 0 || fromIndex >= players.length) return;
    dispatch({ type: "removePlayer", index: fromIndex });
    onSelect(Math.max(0, Math.min(fromIndex, players.length - 2)));
  };

  const handleSeatPointerUp = (event: PointerEvent<HTMLDivElement>, index: number, player: string) => {
    if (event.pointerType === "mouse" || editingIndex === index) return;
    const now = Date.now();
    if (lastSeatTap.current.index === index && now - lastSeatTap.current.time <= DOUBLE_TAP_WINDOW_MS) {
      event.preventDefault();
      beginRename(index, player);
      lastSeatTap.current = { index: -1, time: 0 };
      return;
    }
    lastSeatTap.current = { index, time: now };
  };

  const handleSeatKeyDown = (event: KeyboardEvent<HTMLDivElement>, index: number, player: string) => {
    if (event.key === "Enter" || event.key === " ") {
      event.preventDefault();
      onSelect(index);
    } else if (event.key === "F2") {
      event.preventDefault();
      beginRename(index, player);
    }
  };

  return (
    <div className="sheet-content">
      <div className="sheet-tools">
        <label>
          Players
          <input
            type="number"
            min={0}
            max={20}
            value={players.length}
            onChange={(event) => dispatch({ type: "setPlayerCount", count: Number(event.target.value) })}
          />
        </label>
        <SetupCountSummary setupCounts={setupCounts} />
        {draggedIndex !== undefined && (
          <div
            className={`seat-trash-zone${trashDropActive ? " drop-target" : ""}`}
            aria-label="Trash zone for removing seats"
            onDragEnter={(event) => {
              allowSeatDrop(event);
              setTrashDropActive(true);
            }}
            onDragOver={allowSeatDrop}
            onDragLeave={() => setTrashDropActive(false)}
            onDrop={dropSeatOnTrash}
          >
            <span aria-hidden="true">×</span>
            <strong>Trash</strong>
          </div>
        )}
      </div>

      <div className="seating-chart" aria-label="Clockwise seating chart">
        <div className="seating-ring" />
        {players.map((player, index) => {
          const roleClaims = claimIndexesForPlayer(doc, player);
          const roleLabels = roleClaims.map(([claim]) => roleEmojiLabel(claim.type));
          const primaryClaim = mostRecentClaim(roleClaims);
          const deathMarker = deathMarkerForPlayer(doc.timeline, player);
          const deathClass = deathMarker === undefined ? undefined : deathMarkerClass(deathMarker);
          const deathLabel = deathMarker === undefined ? "" : `, ${deathMarkerLabel(deathMarker)}`;
          const isEditing = editingIndex === index;
          return (
            <div
              key={player}
              className={`seat-button${deathClass === undefined ? "" : ` death-${deathClass}`}${
                index === selectedIndex ? " selected" : ""
              }${index === draggedIndex ? " dragging" : ""}${isEditing ? " editing" : ""}`}
              style={seatButtonStyle(index, players.length, player)}
              draggable={!isEditing}
              role="button"
              tabIndex={0}
              onDragStart={(event) => startSeatDrag(event, index)}
              onDragOver={allowSeatDrop}
              onDrop={(event) => dropSeat(event, index)}
              onDragEnd={() => {
                setDraggedIndex(undefined);
                setTrashDropActive(false);
              }}
              onClick={() => onSelect(index)}
              onDoubleClick={() => beginRename(index, player)}
              onPointerUp={(event) => handleSeatPointerUp(event, index, player)}
              onKeyDown={(event) => handleSeatKeyDown(event, index, player)}
              aria-pressed={index === selectedIndex}
              aria-label={`Seat ${index + 1}: ${player}${deathLabel}. Drag to reorder seats. Double-click to rename.`}
            >
              {deathClass !== undefined && <span className={`seat-shroud ${deathClass}`} aria-hidden="true" />}
              <span
                className="seat-token-icon"
                aria-label={
                  roleLabels.length === 0 ? "No claims" : `Primary claim: ${roleEmojiLabel(primaryClaim?.type)}`
                }
                title={roleLabels.join(", ")}
              >
                {roleEmoji(primaryClaim?.type) ?? index + 1}
              </span>
              {isEditing ? (
                <input
                  className="seat-name-input"
                  type="text"
                  value={draftName}
                  autoFocus
                  aria-label={`Rename ${player}`}
                  draggable={false}
                  onFocus={(event) => event.currentTarget.select()}
                  onChange={(event) => setDraftName(event.target.value)}
                  onBlur={commitRename}
                  onClick={(event) => event.stopPropagation()}
                  onDoubleClick={(event) => event.stopPropagation()}
                  onPointerUp={(event) => event.stopPropagation()}
                  onKeyDown={(event) => {
                    event.stopPropagation();
                    if (event.key === "Enter") {
                      event.preventDefault();
                      commitRename();
                    } else if (event.key === "Escape") {
                      event.preventDefault();
                      cancelRename();
                    }
                  }}
                />
              ) : (
                <span className="seat-player-name">{player}</span>
              )}
              {deathMarker !== undefined && deathClass !== undefined && (
                <span className={`seat-death-badge ${deathClass}`} aria-hidden="true">
                  {timelineEventGlyph(deathMarker)}
                </span>
              )}
            </div>
          );
        })}

        {chartQuoteCards.map((card) => (
          <button
            key={`${card.claimIndex}-${card.player}-callout`}
            type="button"
            className="claim-callout"
            style={calloutPosition(card.playerIndex, players.length)}
            onClick={() => onSelect(card.playerIndex)}
          >
            "{card.summary}"
          </button>
        ))}

        <div className="center-timeline" aria-live="polite">
          <strong>{selectedName ?? "No player selected"}</strong>
          <span>Click tokens to edit claims</span>
        </div>
      </div>

      <ClaimQuoteDeck cards={quoteCards} onSelect={onSelect} />

      {hasTimeline && (
        <>
          <div className="sheet-divider" />
          <TimelineStrip timeline={doc.timeline ?? []} />
        </>
      )}
    </div>
  );
}

function ClaimQuoteDeck({ cards, onSelect }: { cards: readonly ClaimQuoteCard[]; onSelect: (index: number) => void }) {
  if (cards.length === 0) return null;

  return (
    <section className="claim-summary-deck" aria-label="Player claim summaries">
      <h3>Claims</h3>
      <div className="claim-summary-grid">
        {cards.map((card) => (
          <button
            key={`${card.claimIndex}-${card.player}-summary`}
            type="button"
            className="claim-summary-card"
            onClick={() => onSelect(card.playerIndex)}
          >
            <span className="claim-summary-meta">
              <strong>{card.player}</strong>
              <span>{card.roleLabel}</span>
            </span>
            <span className="claim-summary-text">"{card.summary}"</span>
          </button>
        ))}
      </div>
    </section>
  );
}

export function DrawWorkbench({ doc, dispatch, selectedIndex }: DrawWorkbenchProps) {
  const players = doc.players;
  const [newType, setNewType] = useState<Claim["type"]>("Investigator");
  const selectedName = players[selectedIndex];
  const selectedClaims = selectedName === undefined ? [] : claimIndexesForPlayer(doc, selectedName);

  const addClaim = () => {
    if (selectedName === undefined) return;
    dispatch({ type: "addClaim", claim: makeEmptyClaim(newType, selectedName) });
  };

  return (
    <div className="draw-workbench">
      <section className="panel claims-panel">
        <header className="panel-heading-row">
          <div>
            <h3>Claims</h3>
            <span>{selectedClaims.length} for selected player</span>
          </div>
          <button type="button" onClick={addClaim} disabled={selectedName === undefined}>
            Add Claim
          </button>
        </header>
        <div className="claim-add-row">
          <select value={newType} onChange={(event) => setNewType(event.target.value as Claim["type"])}>
            {CLAIM_TYPES.map((type) => (
              <option key={type} value={type}>
                {type}
              </option>
            ))}
          </select>
        </div>
        <div className="selected-claims">
          {selectedName !== undefined && selectedClaims.length === 0 && <p>No claims for {selectedName}.</p>}
          {selectedClaims.map(([claim, index]) => (
            <div key={index} className="claim-block">
              <header>
                <strong>{roleEmojiLabel(claim.type)}</strong>
                <button type="button" onClick={() => dispatch({ type: "removeClaim", index })}>
                  Remove
                </button>
              </header>
              <ClaimBody
                doc={doc}
                claim={claim}
                onChange={(nextClaim) => dispatch({ type: "updateClaim", index, claim: nextClaim })}
              />
            </div>
          ))}
        </div>
      </section>

      <HiddenRolesTray roles={doc.script} />
    </div>
  );
}

function HiddenRolesTray({ roles }: { roles: readonly string[] }) {
  const selected = new Set(roles);
  const hiddenRoles = hiddenScriptRoleOptions().filter((role) => selected.has(role));

  return (
    <section className="panel hidden-role-tray">
      <header className="panel-heading-row">
        <div>
          <h3>Potential hidden roles</h3>
          <span>{hiddenRoles.length} roles</span>
        </div>
      </header>
      <div className="role-palette script-role-palette">
        {hiddenRoles.map((role) => {
          const type = ROLE_CLASSES.get(role)?.characterType;
          return (
            <div key={role} className="role-stamp selected hidden-role-preview" aria-label={role}>
              <span aria-hidden="true">{roleEmoji(role) ?? "?"}</span>
              <small>{role}</small>
              {type !== undefined && <em>{TYPE_LABEL[type]}</em>}
            </div>
          );
        })}
        {hiddenRoles.length === 0 && <p className="palette-empty">No hidden roles selected.</p>}
      </div>
    </section>
  );
}

function SetupCountSummary({ setupCounts }: { setupCounts: Record<CharacterType, number> }) {
  return (
    <div className="setup-counts" aria-label="Setup role counts">
      <SetupCountPill label="Townsfolk" count={setupCounts.townsfolk} />
      <SetupCountPill label="Outsider" count={setupCounts.outsider} />
      <SetupCountPill label="Minion" count={setupCounts.minion} tone="evil" />
      <SetupCountPill label="Demon" count={setupCounts.demon} tone="evil" />
    </div>
  );
}

function SetupCountPill({ label, count, tone = "good" }: { label: string; count: number; tone?: "good" | "evil" }) {
  return (
    <span className={`setup-count-pill ${tone}`} aria-label={`${count} ${label}`}>
      <strong>{count}</strong>
      {label}
    </span>
  );
}

function TimelineStrip({ timeline }: { timeline: readonly TimelineEventDoc[] }) {
  const deathCount = timeline.reduce((sum, event) => sum + event.players.length, 0);
  return (
    <div className="timeline-strip" aria-label="Puzzle timeline">
      <div className="timeline-legend">
        <strong>Timeline</strong>
        <span>Deaths and executions</span>
      </div>
      <ol className="timeline-event-list">
        {timeline.map((event, index) => {
          const deathClass = deathMarkerClass(event);
          return (
            <li
              key={`${event.timing}-${event.type}-${index}`}
              className={`timeline-event ${deathClass}`}
              aria-label={`${timingLabel(event.timing)} ${timelineEventAction(event)}: ${event.players.join(", ")}`}
            >
              <span className={`timeline-node ${deathClass}`} aria-hidden="true">
                {timelineEventGlyph(event)}
              </span>
              <div>
                <strong>
                  {compactTimingLabel(event.timing)} {timelineEventAction(event)}
                </strong>
                <span>{formatList(event.players)}</span>
              </div>
            </li>
          );
        })}
      </ol>
      <div className="sheet-footnote">
        {deathCount} death{deathCount === 1 ? "" : "s"} tracked
      </div>
    </div>
  );
}

function claimIndexesForPlayer(doc: PuzzleDoc, player: string): Array<[Claim, number]> {
  return doc.claims.flatMap((claim, index) => (claim.name === player ? [[claim, index] as [Claim, number]] : []));
}

function mostRecentClaim(claims: Array<[Claim, number]>): Claim | undefined {
  return claims.reduce<[Claim, number] | undefined>(
    (latest, entry) => (latest === undefined || entry[1] > latest[1] ? entry : latest),
    undefined,
  )?.[0];
}

function claimQuoteCardsForDoc(doc: PuzzleDoc): ClaimQuoteCard[] {
  return doc.claims.flatMap((claim, claimIndex) => {
    const playerIndex = doc.players.indexOf(claim.name);
    if (playerIndex === -1) return [];
    return [
      {
        player: claim.name,
        playerIndex,
        claimIndex,
        roleLabel: roleEmojiLabel(claim.type),
        summary: claimSummary(claim),
      },
    ];
  });
}

function firstQuoteCardsByPlayer(cards: readonly ClaimQuoteCard[]): ClaimQuoteCard[] {
  const seen = new Set<string>();
  return cards.filter((card) => {
    if (seen.has(card.player)) return false;
    seen.add(card.player);
    return true;
  });
}

function deathMarkerForPlayer(timeline: PuzzleDoc["timeline"], player: string): TimelineEventDoc | undefined {
  const events = timeline ?? [];
  const nominationDeath = events.find((event) => event.type === "nominationDeath" && event.players.includes(player));
  if (nominationDeath !== undefined) return nominationDeath;
  const execution = events.find((event) => event.type === "execution" && event.players.includes(player));
  if (execution !== undefined) return execution;
  const nightDeath = events.find((event) => event.type === "nightDeath" && event.players.includes(player));
  if (nightDeath !== undefined) return nightDeath;
  const abilityDeath = events.find((event) => event.type === "abilityDeath" && event.players.includes(player));
  if (abilityDeath !== undefined) return abilityDeath;
  const nightKill = events.find((event) => event.type === "nightKill" && event.players.includes(player));
  if (nightKill !== undefined) return nightKill;
  return events.find((event) => event.type === "nightKillBeforeInfo" && event.players.includes(player));
}

function visibleTimelineEventType(event: TimelineEventDoc): TimelineEventDoc["type"] {
  return event.type === "abilityDeath" && event.timing.startsWith("night_") ? "nightKill" : event.type;
}

function deathMarkerClass(event: TimelineEventDoc): "nomination-death" | "execution" | "night-kill" {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "nomination-death";
  return type === "execution" ? "execution" : "night-kill";
}

function deathMarkerLabel(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "died while nominating";
  if (type === "execution") return "executed";
  if (type === "abilityDeath") return "died from an ability";
  return "killed at night";
}

function timelineEventAction(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "Nomination Death";
  if (type === "execution") return "Execution";
  if (type === "abilityDeath") return "Ability Death";
  return event.players.length === 1 ? "Night Death" : "Night Deaths";
}

function timelineEventGlyph(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "!";
  if (type === "execution") return "X";
  if (type === "abilityDeath") return "*";
  return "N";
}

function seatPosition(index: number, count: number): CSSProperties {
  if (count === 0) return {};
  const angle = -90 + (index * 360) / count;
  const radians = (angle * Math.PI) / 180;
  const radius = 36;
  return {
    left: `${50 + Math.cos(radians) * radius}%`,
    top: `${50 + Math.sin(radians) * radius}%`,
  };
}

function seatButtonStyle(index: number, count: number, player: string): CSSProperties {
  return {
    ...seatPosition(index, count),
    "--seat-name-scale": Math.min(1, 6.6 / Math.max(player.length, 1)).toFixed(3),
  } as CSSProperties;
}

function calloutPosition(index: number, count: number): CSSProperties {
  if (count === 0) return {};
  const angle = -90 + (index * 360) / count;
  const radians = (angle * Math.PI) / 180;
  const radiusX = 50;
  const radiusY = 50;
  return {
    left: `${50 + Math.cos(radians) * radiusX}%`,
    top: `${50 + Math.sin(radians) * radiusY}%`,
  };
}

function countSetupRoles(doc: PuzzleDoc): Record<CharacterType, number> {
  if (doc.setup === "none" || doc.setup === "atheist") return countScriptRoles(doc.script);
  try {
    return { ...standardSetupCounts(doc.players.length) };
  } catch {
    return countScriptRoles(doc.script);
  }
}

function countScriptRoles(script: readonly string[]): Record<CharacterType, number> {
  const counts: Record<CharacterType, number> = {
    [CharacterType.Townsfolk]: 0,
    [CharacterType.Outsider]: 0,
    [CharacterType.Minion]: 0,
    [CharacterType.Demon]: 0,
  };
  for (const role of script) {
    const characterType = ROLE_CLASSES.get(role)?.characterType;
    if (characterType !== undefined) counts[characterType] += 1;
  }
  return counts;
}
