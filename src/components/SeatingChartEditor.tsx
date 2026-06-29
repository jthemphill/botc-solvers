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
import type { Claim, PuzzleDoc, TimelineEventDoc, TimelineEventType } from "../schema/puzzleDoc";
import { sortTimelineEvents, type PuzzleAction } from "../state/puzzleDoc";
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
const TIMELINE_DAY_OPTIONS = ["day_1", "day_2", "day_3", "day_4", "day_5"];
const TIMELINE_NIGHT_OPTIONS = ["night_1", "night_2", "night_3", "night_4", "night_5"];
const TIMELINE_EVENT_TYPE_OPTIONS: Array<{ type: TimelineEventType; label: string }> = [
  { type: "execution", label: "Execution" },
  { type: "nightDeath", label: "Night Death" },
  { type: "slayerShot", label: "Slayer Shot" },
  { type: "witchCurse", label: "Witch Curse" },
  { type: "nominationDeath", label: "Nomination Death" },
  { type: "doomsayerDeath", label: "Doomsayer Death" },
];

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
  const timeline = doc.timeline ?? [];
  const [draggedIndex, setDraggedIndex] = useState<number | undefined>(undefined);
  const [editingIndex, setEditingIndex] = useState<number | undefined>(undefined);
  const [selectedTimelineIndex, setSelectedTimelineIndex] = useState<number | undefined>(undefined);
  const [draftName, setDraftName] = useState("");
  const [trashDropActive, setTrashDropActive] = useState(false);
  const lastSeatTap = useRef<{ index: number; time: number }>({ index: -1, time: 0 });
  const quoteCards = claimQuoteCardsForDoc(doc);
  const chartQuoteCards = players.length <= 10 ? mergedQuoteCardsByPlayer(quoteCards) : [];

  useEffect(() => {
    if (selectedIndex >= players.length) onSelect(Math.max(0, players.length - 1));
  }, [onSelect, players.length, selectedIndex]);

  useEffect(() => {
    if (editingIndex !== undefined && editingIndex >= players.length) {
      setEditingIndex(undefined);
      setDraftName("");
    }
  }, [editingIndex, players.length]);

  useEffect(() => {
    if (selectedTimelineIndex !== undefined && selectedTimelineIndex >= timeline.length) {
      setSelectedTimelineIndex(timeline.length === 0 ? undefined : timeline.length - 1);
    }
  }, [selectedTimelineIndex, timeline.length]);

  const setTimeline = (next: PuzzleDoc["timeline"]) => {
    dispatch({ type: "setTimeline", timeline: next });
  };

  const updateTimelineEvent = (index: number, event: TimelineEventDoc) => {
    const nextTimeline = sortTimelineEvents(
      timeline.map((entry, eventIndex) => (eventIndex === index ? event : entry)),
    );
    setTimeline(nextTimeline);
    const nextIndex = nextTimeline.indexOf(event);
    setSelectedTimelineIndex(nextIndex === -1 ? undefined : nextIndex);
  };

  const removeTimelineEvent = (index: number) => {
    setTimeline(timeline.filter((_, eventIndex) => eventIndex !== index));
    setSelectedTimelineIndex((current) => {
      if (current === undefined) return undefined;
      if (current === index) return undefined;
      return current > index ? current - 1 : current;
    });
  };

  const dropSeatOnTimeline = (
    event: DragEvent<HTMLElement>,
    type: Extract<TimelineEventType, "execution" | "nightDeath">,
  ) => {
    event.preventDefault();
    const fromIndex = draggedSeatIndex(event);
    setDraggedIndex(undefined);
    setTrashDropActive(false);
    if (fromIndex === undefined || fromIndex < 0 || fromIndex >= players.length) return;
    const player = players[fromIndex];
    if (player === undefined) return;
    const nextEvent: TimelineEventDoc = {
      timing: nextTimelineTiming(timeline, type),
      type,
      players: [player],
    };
    const nextTimeline = sortTimelineEvents([...timeline, nextEvent]);
    setTimeline(nextTimeline);
    const nextIndex = nextTimeline.indexOf(nextEvent);
    setSelectedTimelineIndex(nextIndex === -1 ? undefined : nextIndex);
  };

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
          <PlayerCountInput value={players.length} onChange={(count) => dispatch({ type: "setPlayerCount", count })} />
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

      <div className="sheet-divider" />
      <TimelineStrip
        timeline={timeline}
        players={players}
        selectedIndex={selectedTimelineIndex}
        onSelect={setSelectedTimelineIndex}
        onUpdate={updateTimelineEvent}
        onRemove={removeTimelineEvent}
        onDropPlayer={dropSeatOnTimeline}
        onAllowDrop={allowSeatDrop}
      />
    </div>
  );
}

function PlayerCountInput({ value, onChange }: { value: number; onChange: (value: number) => void }) {
  const [draft, setDraft] = useState(String(value));
  const [focused, setFocused] = useState(false);

  useEffect(() => {
    if (!focused) setDraft(String(value));
  }, [focused, value]);

  const commit = () => {
    setFocused(false);
    if (draft === "") {
      setDraft(String(value));
      return;
    }
    const next = Number(draft);
    if (Number.isFinite(next)) onChange(next);
    setDraft(String(Number.isFinite(next) ? Math.max(0, Math.floor(next)) : value));
  };

  return (
    <input
      type="number"
      min={0}
      max={20}
      value={draft}
      onFocus={() => setFocused(true)}
      onChange={(event) => {
        const nextDraft = event.target.value;
        if (nextDraft === "") {
          setDraft("");
          return;
        }
        const next = Number(nextDraft);
        if (!Number.isFinite(next)) {
          setDraft(nextDraft);
          return;
        }
        const normalized = Math.max(0, Math.floor(next));
        setDraft(String(normalized));
        onChange(normalized);
      }}
      onBlur={commit}
    />
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

function TimelineTimingSelect({
  type,
  value,
  onChange,
}: {
  type: TimelineEventType;
  value: string;
  onChange: (timing: string) => void;
}) {
  return (
    <select value={value} onChange={(event) => onChange(event.target.value)}>
      {timingOptionsForType(type, value).map((timing) => (
        <option key={timing} value={timing}>
          {timingLabel(timing)}
        </option>
      ))}
    </select>
  );
}

function TimelinePlayerPicker({
  players,
  value,
  onChange,
  maxSelections,
}: {
  players: readonly string[];
  value: readonly string[];
  onChange: (players: readonly string[]) => void;
  maxSelections?: number;
}) {
  return (
    <div className="timeline-player-picker">
      {players.map((player) => {
        const selected = value.includes(player);
        const limitReached = maxSelections !== undefined && value.length >= maxSelections;
        return (
          <label key={player}>
            <input
              type="checkbox"
              checked={selected}
              disabled={!selected && limitReached}
              onChange={(event) => {
                if (event.target.checked) {
                  if (!selected && (maxSelections === undefined || value.length < maxSelections)) {
                    onChange([...value, player]);
                  }
                  return;
                }
                onChange(value.filter((name) => name !== player));
              }}
            />
            {player}
          </label>
        );
      })}
    </div>
  );
}

function defaultTimingForType(type: TimelineEventType, currentTiming: string): string {
  if (type === "nightDeath") return currentTiming.startsWith("night_") ? currentTiming : "night_2";
  return currentTiming.startsWith("day_") ? currentTiming : "day_1";
}

function timingOptionsForType(type: TimelineEventType, currentTiming: string): readonly string[] {
  const base = type === "nightDeath" ? TIMELINE_NIGHT_OPTIONS : TIMELINE_DAY_OPTIONS;
  return base.includes(currentTiming) ? base : [currentTiming, ...base];
}

function normalizeTimelinePlayers(type: TimelineEventType, players: readonly string[]): readonly string[] {
  const uniquePlayers = players.filter((player, index) => players.indexOf(player) === index);
  return type === "nightDeath" ? uniquePlayers : uniquePlayers.slice(0, 1);
}

function nextTimelineTiming(
  timeline: readonly TimelineEventDoc[],
  type: Extract<TimelineEventType, "execution" | "nightDeath">,
): string {
  const prefix = type === "execution" ? "day" : "night";
  const fallback = type === "execution" ? 1 : 2;
  const latest = timeline.reduce((max, event) => {
    const match = new RegExp(`^${prefix}_(\\d+)$`).exec(event.timing);
    if (match === null) return max;
    return Math.max(max, Number(match[1]));
  }, 0);
  return `${prefix}_${Math.max(fallback, latest + 1)}`;
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

function TimelineStrip({
  timeline,
  players,
  selectedIndex,
  onSelect,
  onUpdate,
  onRemove,
  onDropPlayer,
  onAllowDrop,
}: {
  timeline: readonly TimelineEventDoc[];
  players: readonly string[];
  selectedIndex: number | undefined;
  onSelect: (index: number | undefined) => void;
  onUpdate: (index: number, event: TimelineEventDoc) => void;
  onRemove: (index: number) => void;
  onDropPlayer: (event: DragEvent<HTMLElement>, type: Extract<TimelineEventType, "execution" | "nightDeath">) => void;
  onAllowDrop: (event: DragEvent<HTMLElement>) => void;
}) {
  const deathCount = timeline.reduce((sum, event) => sum + event.players.length, 0);
  const selectedEvent = selectedIndex === undefined ? undefined : timeline[selectedIndex];
  return (
    <div className="timeline-strip" aria-label="Puzzle timeline">
      <div
        className="timeline-drop-zone execution"
        onDragEnter={onAllowDrop}
        onDragOver={onAllowDrop}
        onDrop={(event) => onDropPlayer(event, "execution")}
      >
        <span aria-hidden="true">X</span>
        <strong>Execution</strong>
        <em>Drop a player here</em>
      </div>

      <div className="timeline-main">
        <div className="timeline-legend">
          <strong>Timeline</strong>
          <span>
            {deathCount} death{deathCount === 1 ? "" : "s"} tracked
          </span>
        </div>
        {timeline.length === 0 ? (
          <p className="timeline-empty">Drag a player to record the first death.</p>
        ) : (
          <ol className="timeline-event-list">
            {timeline.map((event, index) => {
              const deathClass = deathMarkerClass(event);
              const selected = index === selectedIndex;
              return (
                <li key={`${event.timing}-${event.type}-${index}`} className={`timeline-event ${deathClass}`}>
                  <button
                    type="button"
                    className={selected ? "selected" : undefined}
                    aria-pressed={selected}
                    aria-label={`${timingLabel(event.timing)} ${timelineEventAction(event)}: ${event.players.join(", ")}`}
                    onClick={() => onSelect(selected ? undefined : index)}
                  >
                    <span className={`timeline-node ${deathClass}`} aria-hidden="true">
                      {timelineEventGlyph(event)}
                    </span>
                    <span className="timeline-event-card">
                      <strong>
                        {compactTimingLabel(event.timing)} {timelineEventAction(event)}
                      </strong>
                      <span>{formatList(event.players)}</span>
                    </span>
                  </button>
                </li>
              );
            })}
          </ol>
        )}

        {selectedEvent !== undefined && selectedIndex !== undefined && (
          <TimelineEventDetails
            event={selectedEvent}
            players={players}
            onChange={(event) => onUpdate(selectedIndex, event)}
            onRemove={() => onRemove(selectedIndex)}
          />
        )}
      </div>

      <div
        className="timeline-drop-zone night-kill"
        onDragEnter={onAllowDrop}
        onDragOver={onAllowDrop}
        onDrop={(event) => onDropPlayer(event, "nightDeath")}
      >
        <span aria-hidden="true">N</span>
        <strong>Night Death</strong>
        <em>Drop a player here</em>
      </div>
    </div>
  );
}

function TimelineEventDetails({
  event,
  players,
  onChange,
  onRemove,
}: {
  event: TimelineEventDoc;
  players: readonly string[];
  onChange: (event: TimelineEventDoc) => void;
  onRemove: () => void;
}) {
  const setType = (type: TimelineEventType) => {
    onChange({
      ...event,
      type,
      timing: defaultTimingForType(type, event.timing),
      players: normalizeTimelinePlayers(type, event.players),
      caller: type === "doomsayerDeath" ? event.caller : undefined,
    });
  };

  return (
    <div className="timeline-event-details">
      <label>
        Cause
        <select value={event.type} onChange={(changeEvent) => setType(changeEvent.target.value as TimelineEventType)}>
          {TIMELINE_EVENT_TYPE_OPTIONS.map((option) => (
            <option key={option.type} value={option.type}>
              {option.label}
            </option>
          ))}
        </select>
      </label>
      <label>
        Timing
        <TimelineTimingSelect
          type={event.type}
          value={event.timing}
          onChange={(timing) => onChange({ ...event, timing })}
        />
      </label>
      <div className="timeline-detail-players">
        <span>Players</span>
        <TimelinePlayerPicker
          players={players}
          value={event.players}
          onChange={(nextPlayers) => onChange({ ...event, players: normalizeTimelinePlayers(event.type, nextPlayers) })}
          maxSelections={event.type === "nightDeath" ? undefined : 1}
        />
      </div>
      {event.type === "doomsayerDeath" && (
        <label>
          Caller
          <select
            value={event.caller ?? ""}
            onChange={(changeEvent) => onChange({ ...event, caller: changeEvent.target.value || undefined })}
          >
            <option value="">-</option>
            {players.map((player) => (
              <option key={player} value={player}>
                {player}
              </option>
            ))}
          </select>
        </label>
      )}
      <button type="button" onClick={onRemove}>
        Remove Event
      </button>
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

function mergedQuoteCardsByPlayer(cards: readonly ClaimQuoteCard[]): ClaimQuoteCard[] {
  const mergedCards: ClaimQuoteCard[] = [];
  const cardIndexesByPlayer = new Map<string, number>();

  for (const card of cards) {
    const index = cardIndexesByPlayer.get(card.player);
    if (index === undefined) {
      cardIndexesByPlayer.set(card.player, mergedCards.length);
      mergedCards.push(card);
      continue;
    }

    const existing = mergedCards[index];
    if (existing === undefined) continue;
    const roleLabels = existing.roleLabel.split(", ");
    mergedCards[index] = {
      ...existing,
      roleLabel: roleLabels.includes(card.roleLabel) ? existing.roleLabel : `${existing.roleLabel}, ${card.roleLabel}`,
      summary: `${existing.summary}; ${card.summary}`,
    };
  }

  return mergedCards;
}

function deathMarkerForPlayer(timeline: PuzzleDoc["timeline"], player: string): TimelineEventDoc | undefined {
  const events = timeline ?? [];
  const nominationDeath = events.find((event) => event.type === "nominationDeath" && event.players.includes(player));
  if (nominationDeath !== undefined) return nominationDeath;
  const witchCurse = events.find((event) => event.type === "witchCurse" && event.players.includes(player));
  if (witchCurse !== undefined) return witchCurse;
  const slayerShot = events.find((event) => event.type === "slayerShot" && event.players.includes(player));
  if (slayerShot !== undefined) return slayerShot;
  const execution = events.find((event) => event.type === "execution" && event.players.includes(player));
  if (execution !== undefined) return execution;
  const nightDeath = events.find((event) => event.type === "nightDeath" && event.players.includes(player));
  if (nightDeath !== undefined) return nightDeath;
  return undefined;
}

function visibleTimelineEventType(event: TimelineEventDoc): TimelineEventDoc["type"] {
  return event.type;
}

function deathMarkerClass(
  event: TimelineEventDoc,
): "nomination-death" | "witch-curse" | "slayer-shot" | "execution" | "night-kill" {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "nomination-death";
  if (type === "witchCurse") return "witch-curse";
  if (type === "slayerShot") return "slayer-shot";
  return type === "execution" ? "execution" : "night-kill";
}

function deathMarkerLabel(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "died while nominating";
  if (type === "witchCurse") return "died to a Witch curse";
  if (type === "slayerShot") return "died to a Slayer shot";
  if (type === "execution") return "executed";
  return "killed at night";
}

function timelineEventAction(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "Nomination Death";
  if (type === "witchCurse") return "Witch Curse";
  if (type === "slayerShot") return "Slayer Shot";
  if (type === "execution") return "Execution";
  return event.players.length === 1 ? "Night Death" : "Night Deaths";
}

function timelineEventGlyph(event: TimelineEventDoc): string {
  const type = visibleTimelineEventType(event);
  if (type === "nominationDeath") return "!";
  if (type === "witchCurse") return "🪄";
  if (type === "slayerShot") return "🏹";
  if (type === "execution") return "X";
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
