import { Fragment, useId, useState, type Dispatch } from "react";
import { DslError, lex } from "../dsl/lex";
import { parse } from "../dsl/parse";
import { Alignment, CharacterType } from "../model/core";
import { roleEmojiLabel } from "../model/roleEmoji";
import { ROLE_CLASSES } from "../model/roleRegistry";
import { canonicalRoleName, jugglerGuessRoleOptions } from "../state/scriptRoles";
import type {
  AcrobatChoiceDoc,
  BalloonistClaim,
  ChambermaidCheckDoc,
  Claim,
  ClockmakerClaim,
  CourtierClaim,
  CustomInfoStatementDoc,
  ChefClaim,
  DreamerClaim,
  EmpathClaim,
  ExorcistChoiceDoc,
  ExorcistClaim,
  FlowergirlClaim,
  FlowergirlVoteDoc,
  FortuneTellerCheckDoc,
  FortuneTellerClaim,
  GamblerGuessDoc,
  GossipStatementDoc,
  InvestigatorClaim,
  JugglerClaim,
  KlutzClaim,
  LegionaryCountDoc,
  LegionaryClaim,
  KnightClaim,
  LibrarianClaim,
  MathematicianClaim,
  NightwatchmanClaim,
  NobleClaim,
  OracleClaim,
  PhilosopherClaim,
  PrincessNominationDoc,
  PrincessClaim,
  ProdigyCheckDoc,
  ProdigyClaim,
  PuzzlemasterClaim,
  PuzzlemasterGuessDoc,
  PuzzleDoc,
  RavenkeeperClaim,
  SageClaim,
  SavantClaim,
  SeamstressClaim,
  ShugenjaClaim,
  SlayerClaim,
  SnakeCharmerClaim,
  StewardClaim,
  UndertakerClaim,
  VirginClaim,
  VillageIdiotClaim,
  WasherwomanClaim,
} from "../schema/puzzleDoc";
import { SUPPORTED_CLAIM_TYPES } from "../schema/puzzleDoc";
import type { PuzzleAction } from "../state/puzzleDoc";
import { RoleListEditor, RoleTypeahead, sortedRoleNames } from "./RolePicker";

interface Props {
  doc: PuzzleDoc;
  dispatch: Dispatch<PuzzleAction>;
}

export const CLAIM_TYPES = [...SUPPORTED_CLAIM_TYPES];

const TIMING_OPTIONS = [
  "night_1",
  "day_1",
  "night_2",
  "day_2",
  "night_3",
  "day_3",
  "night_4",
  "day_4",
  "night_5",
  "day_5",
];

function timingLabel(timing: string): string {
  const match = /^(night|day)_(\d+)$/.exec(timing);
  if (match === null) return timing;
  const [, period, number] = match;
  if (period === undefined || number === undefined) return timing;
  return `${period[0]?.toUpperCase()}${period.slice(1)} ${number}`;
}

export function ClaimsEditor({ doc, dispatch }: Props) {
  const [newType, setNewType] = useState<Claim["type"]>("Investigator");
  const [newName, setNewName] = useState<string>("");

  const addClaim = () => {
    const name = newName || doc.players[0] || "";
    if (!name) return;
    const claim = makeEmptyClaim(newType, name);
    dispatch({ type: "addClaim", claim });
  };

  return (
    <section className="panel">
      <h3>Claims</h3>
      <div className="row">
        <select
          id="claim-type"
          name="claim-type"
          aria-label="Claim type"
          value={newType}
          onChange={(e) => setNewType(e.target.value as Claim["type"])}
        >
          {CLAIM_TYPES.map((t) => (
            <option key={t} value={t}>
              {t}
            </option>
          ))}
        </select>
        <select
          id="claim-player"
          name="claim-player"
          aria-label="Claiming player"
          value={newName}
          onChange={(e) => setNewName(e.target.value)}
        >
          <option value="">— player —</option>
          {doc.players.map((p) => (
            <option key={p} value={p}>
              {p}
            </option>
          ))}
        </select>
        <button onClick={addClaim} disabled={doc.players.length === 0}>
          + Add claim
        </button>
      </div>
      {doc.claims.map((c, i) => (
        <div key={i} className="claim-block">
          <header>
            <strong>
              {c.name} — {roleEmojiLabel(c.type)}
            </strong>
            <button onClick={() => dispatch({ type: "removeClaim", index: i })}>Remove</button>
          </header>
          <ClaimBody doc={doc} claim={c} onChange={(claim) => dispatch({ type: "updateClaim", index: i, claim })} />
        </div>
      ))}
    </section>
  );
}

export function makeEmptyClaim(type: Claim["type"], name: string): Claim {
  switch (type) {
    case "Acrobat":
      return { type: "Acrobat", name, choices: [] };
    case "Investigator":
      return { type: "Investigator", name, among: [] };
    case "Librarian":
      return { type: "Librarian", name };
    case "Washerwoman":
      return { type: "Washerwoman", name, among: [] };
    case "Chambermaid":
      return { type: "Chambermaid", name, checks: [] };
    case "Chef":
      return { type: "Chef", name, count: 0 };
    case "Empath":
      return { type: "Empath", name, count: 0 };
    case "Exorcist":
      return { type: "Exorcist", name, choices: [] };
    case "Flowergirl":
      return { type: "Flowergirl", name, votes: [] };
    case "FortuneTeller":
      return { type: "FortuneTeller", name, checks: [{ left: "", right: "", yes: false }] };
    case "Undertaker":
      return { type: "Undertaker", name, player: "", role: "" };
    case "Legionary":
      return { type: "Legionary", name, counts: [] };
    case "Noble":
      return { type: "Noble", name, oneEvilAmong: [] };
    case "Oracle":
      return { type: "Oracle", name };
    case "Philosopher":
      return { type: "Philosopher", name, timing: "night_1", role: "" };
    case "Princess":
      return { type: "Princess", name, nominations: [] };
    case "Prodigy":
      return { type: "Prodigy", name, checks: [] };
    case "Puzzlemaster":
      return { type: "Puzzlemaster", name, guesses: [] };
    case "Steward":
      return { type: "Steward", name, goodPlayer: "" };
    case "Knight":
      return { type: "Knight", name, noDemonAmong: [] };
    case "Seamstress":
      return { type: "Seamstress", name, among: ["", ""], aligned: true };
    case "Juggler":
      return { type: "Juggler", name, timing: "night_2", guesses: {} };
    case "Dreamer":
      return { type: "Dreamer", name, player: "", roles: [] };
    case "Shugenja":
      return { type: "Shugenja", name, evilDirection: "clockwise" };
    case "Clockmaker":
      return { type: "Clockmaker", name, distance: 1 };
    case "Courtier":
      return { type: "Courtier", name, timing: "night_1", role: "", drunkTimings: ["night_1"] };
    case "Mathematician":
      return { type: "Mathematician", name, malfunctions: [{ timing: "night_1", count: 0 }] };
    case "Ravenkeeper":
      return { type: "Ravenkeeper", name, player: "", role: "", timing: "night_2" };
    case "Sage":
      return { type: "Sage", name, demonAmong: [] };
    case "Slayer":
      return { type: "Slayer", name, timing: "day_1", killed: false };
    case "Snake Charmer":
      return { type: "Snake Charmer", name, checks: [{ player: "", demon: false, timing: "night_1" }] };
    case "VillageIdiot":
      return { type: "VillageIdiot", name, checks: [] };
    case "Klutz":
      return { type: "Klutz", name };
    case "Virgin":
      return { type: "Virgin", name, timing: "day_1" };
    case "Balloonist":
      return { type: "Balloonist", name, differentCharacterTypePairs: [] };
    case "Savant":
      return { type: "Savant", name, timing: "day_1", statements: [{ options: ["", ""] }] };
    case "Gambler":
      return { type: "Gambler", name, guesses: [] };
    case "Gossip":
      return { type: "Gossip", name, statements: [] };
    case "Nightwatchman":
      return { type: "Nightwatchman", name, timing: "night_1" };
    default:
      return { type, name } as Claim;
  }
}

interface BodyProps {
  doc: PuzzleDoc;
  claim: Claim;
  onChange: (c: Claim) => void;
}

function TimingField({
  value,
  onChange,
  defaultValue = "night_1",
}: {
  value?: string;
  onChange: (v?: string) => void;
  defaultValue?: string;
}) {
  return (
    <select value={value ?? defaultValue} onChange={(e) => onChange(e.target.value)}>
      {TIMING_OPTIONS.map((t) => (
        <option key={t} value={t}>
          {timingLabel(t)}
        </option>
      ))}
    </select>
  );
}

function MultiPlayerSelect({
  players,
  value,
  onChange,
  maxSelections,
}: {
  players: readonly string[];
  value: readonly string[];
  onChange: (v: readonly string[]) => void;
  maxSelections?: number;
}) {
  return (
    <div className="row">
      {players.map((p) => {
        const selected = value.includes(p);
        const limitReached = maxSelections !== undefined && value.length >= maxSelections;
        return (
          <label key={p} style={{ display: "inline-flex", gap: "0.2rem" }}>
            <input
              type="checkbox"
              checked={selected}
              disabled={!selected && limitReached}
              onChange={(e) => {
                if (e.target.checked) {
                  if (!selected && (maxSelections === undefined || value.length < maxSelections))
                    onChange([...value, p]);
                } else {
                  onChange(value.filter((n) => n !== p));
                }
              }}
            />
            {p}
          </label>
        );
      })}
    </div>
  );
}

function RoleSelect({
  script,
  value,
  onChange,
  allowEmpty = false,
  options,
  ariaLabel = "Role",
}: {
  script: readonly string[];
  value: string | undefined;
  onChange: (v: string) => void;
  allowEmpty?: boolean;
  options?: readonly string[];
  ariaLabel?: string;
}) {
  return (
    <RoleTypeahead
      value={value}
      onChange={onChange}
      allowEmpty={allowEmpty}
      options={options ?? roleOptionsForScript(script)}
      ariaLabel={ariaLabel}
    />
  );
}

function roleOptionsForScript(script: readonly string[]): string[] {
  return sortedRoleNames(script);
}

function roleOptionsByCharacterType(script: readonly string[], types: readonly CharacterType[]): string[] {
  const typeSet = new Set(types);
  return roleOptionsForScript(script).filter((role) => {
    const type = ROLE_CLASSES.get(role)?.characterType;
    return type !== undefined && typeSet.has(type);
  });
}

function PlayerSelect({
  players,
  value,
  onChange,
}: {
  players: readonly string[];
  value: string | undefined;
  onChange: (v: string) => void;
}) {
  return (
    <select value={value ?? ""} onChange={(e) => onChange(e.target.value)}>
      <option value="">—</option>
      {players.map((p) => (
        <option key={p} value={p}>
          {p}
        </option>
      ))}
    </select>
  );
}

export function ClaimBody({ doc, claim, onChange }: BodyProps) {
  const showWidowCall = doc.script.includes("Widow") && isGoodClaimType(claim.type);
  const body = (() => {
    switch (claim.type) {
      case "Acrobat":
        return <AcrobatBody doc={doc} claim={claim} onChange={onChange} />;
      case "Investigator":
        return <InvestigatorBody doc={doc} claim={claim} onChange={onChange} />;
      case "Librarian":
        return <LibrarianBody doc={doc} claim={claim} onChange={onChange} />;
      case "Washerwoman":
        return <WasherwomanBody doc={doc} claim={claim} onChange={onChange} />;
      case "Chambermaid":
        return <ChambermaidBody doc={doc} claim={claim} onChange={onChange} />;
      case "Chef":
        return <ChefBody claim={claim} onChange={onChange} />;
      case "Empath":
        return <EmpathBody doc={doc} claim={claim} onChange={onChange} />;
      case "Exorcist":
        return <ExorcistBody doc={doc} claim={claim} onChange={onChange} />;
      case "Flowergirl":
        return <FlowergirlBody doc={doc} claim={claim} onChange={onChange} />;
      case "FortuneTeller":
        return <FortuneTellerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Undertaker":
        return <UndertakerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Legionary":
        return <LegionaryBody claim={claim} onChange={onChange} />;
      case "Noble":
        return <NobleBody doc={doc} claim={claim} onChange={onChange} />;
      case "Oracle":
        return <OracleBody doc={doc} claim={claim} onChange={onChange} />;
      case "Philosopher":
        return <PhilosopherBody doc={doc} claim={claim} onChange={onChange} />;
      case "Princess":
        return <PrincessBody doc={doc} claim={claim} onChange={onChange} />;
      case "Prodigy":
        return <ProdigyBody doc={doc} claim={claim} onChange={onChange} />;
      case "Puzzlemaster":
        return <PuzzlemasterBody doc={doc} claim={claim} onChange={onChange} />;
      case "Steward":
        return <StewardBody doc={doc} claim={claim} onChange={onChange} />;
      case "Knight":
        return <KnightBody doc={doc} claim={claim} onChange={onChange} />;
      case "Seamstress":
        return <SeamstressBody doc={doc} claim={claim} onChange={onChange} />;
      case "Juggler":
        return <JugglerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Dreamer":
        return <DreamerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Shugenja":
        return <ShugenjaBody claim={claim} onChange={onChange} />;
      case "Clockmaker":
        return <ClockmakerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Courtier":
        return <CourtierBody doc={doc} claim={claim} onChange={onChange} />;
      case "Mathematician":
        return <MathematicianBody claim={claim} onChange={onChange} />;
      case "Ravenkeeper":
        return <RavenkeeperBody doc={doc} claim={claim} onChange={onChange} />;
      case "Sage":
        return <SageBody doc={doc} claim={claim} onChange={onChange} />;
      case "Slayer":
        return <SlayerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Snake Charmer":
        return <SnakeCharmerBody doc={doc} claim={claim} onChange={onChange} />;
      case "VillageIdiot":
        return <VillageIdiotBody doc={doc} claim={claim} onChange={onChange} />;
      case "Klutz":
        return <KlutzBody doc={doc} claim={claim} onChange={onChange} />;
      case "Virgin":
        return <VirginBody doc={doc} claim={claim} onChange={onChange} />;
      case "Balloonist":
        return <BalloonistBody doc={doc} claim={claim} onChange={onChange} />;
      case "Savant":
        return <SavantBody doc={doc} claim={claim} onChange={onChange} />;
      case "Gambler":
        return <GamblerBody doc={doc} claim={claim} onChange={onChange} />;
      case "Gossip":
        return <GossipBody claim={claim} onChange={onChange} />;
      case "Nightwatchman":
        return <NightwatchmanBody doc={doc} claim={claim} onChange={onChange} />;
      default:
        return (
          <div className="field-grid">
            <span>Timing</span>
            <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t } as Claim)} />
          </div>
        );
    }
  })();

  return (
    <>
      {body}
      <AdvancedClaimFields doc={doc} claim={claim} onChange={onChange} />
      {showWidowCall && (
        <label className="checkbox-row">
          <input
            type="checkbox"
            checked={claim.heardWidowCall === true}
            onChange={(event) =>
              onChange({
                ...claim,
                heardWidowCall: event.target.checked ? true : undefined,
              } as Claim)
            }
          />
          <span>Heard the Widow's call</span>
        </label>
      )}
      {claim.type === "Artist" && <CustomInfoEditor claim={claim} onChange={onChange} />}
    </>
  );
}

function isGoodClaimType(type: Claim["type"]): boolean {
  const role = canonicalRoleName(type);
  if (role === undefined) return false;
  return ROLE_CLASSES.get(role)?.alignment === Alignment.Good;
}

function validateDslExpression(src: string): string | undefined {
  if (!src.trim()) return undefined;
  try {
    parse(lex(src));
    return undefined;
  } catch (e) {
    if (e instanceof DslError) return `${e.message} (col ${e.span.start + 1})`;
    return e instanceof Error ? e.message : String(e);
  }
}

function CustomInfoEditor({ claim, onChange }: { claim: Claim; onChange: (c: Claim) => void }) {
  const info = claim.info ?? [];
  const setInfo = (next: readonly CustomInfoStatementDoc[]) => {
    onChange({ ...claim, info: next.length === 0 ? undefined : next } as Claim);
  };
  const updateInfo = (index: number, next: CustomInfoStatementDoc) => {
    setInfo(info.map((entry, i) => (i === index ? next : entry)));
  };
  const removeInfo = (index: number) => {
    setInfo(info.filter((_, i) => i !== index));
  };
  const addInfo = () => {
    setInfo([...info, { timing: claim.timing ?? "night_1", expression: "" }]);
  };

  return (
    <div className="statement-block">
      <header className="row">
        <strong>Info</strong>
        <button type="button" onClick={addInfo}>
          + Add info
        </button>
      </header>
      {info.map((entry, index) => {
        const expressionError = validateDslExpression(entry.expression ?? "");
        return (
          <div key={index} className="field-grid">
            <span>Timing</span>
            <TimingField value={entry.timing} onChange={(timing) => updateInfo(index, { ...entry, timing })} />
            <span>Expression</span>
            <div>
              <textarea
                value={entry.expression ?? ""}
                onChange={(event) => updateInfo(index, { ...entry, expression: event.target.value })}
              />
              {expressionError && <div className="error">{expressionError}</div>}
            </div>
            <span />
            <button type="button" onClick={() => removeInfo(index)}>
              Remove info
            </button>
          </div>
        );
      })}
    </div>
  );
}

function AdvancedClaimFields({ doc, claim, onChange }: BodyProps) {
  const possibleActualRoles = claim.possibleActualRoles ?? [];
  const setPossibleActualRoles = (roles: readonly string[]) => {
    onChange({
      ...claim,
      possibleActualRoles: roles.length === 0 ? undefined : roles,
    });
  };

  return (
    <details className="advanced-claim-fields" open={possibleActualRoles.length > 0}>
      <summary>Advanced</summary>
      <div className="field-grid">
        <span>Possible actual roles</span>
        <RoleListEditor
          value={possibleActualRoles}
          onChange={setPossibleActualRoles}
          options={roleOptionsForScript(doc.script)}
          label="Possible actual roles"
        />
      </div>
    </details>
  );
}

function OptionalBooleanSelect({
  value,
  onChange,
  trueLabel = "yes",
  falseLabel = "no",
}: {
  value: boolean | undefined;
  onChange: (value: boolean | undefined) => void;
  trueLabel?: string;
  falseLabel?: string;
}) {
  return (
    <select
      value={value === undefined ? "" : value ? "true" : "false"}
      onChange={(event) => onChange(event.target.value === "" ? undefined : event.target.value === "true")}
    >
      <option value="">-</option>
      <option value="true">{trueLabel}</option>
      <option value="false">{falseLabel}</option>
    </select>
  );
}

function AcrobatBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: Extract<Claim, { readonly type: "Acrobat" }>;
  onChange: (c: Claim) => void;
}) {
  const choices = claim.choices ?? [];
  const setChoice = (index: number, choice: AcrobatChoiceDoc) =>
    onChange({ ...claim, choices: choices.map((entry, i) => (i === index ? choice : entry)) });
  const addChoice = () =>
    onChange({
      ...claim,
      choices: [...choices, { player: doc.players[0] ?? "", died: false }],
    });
  const removeChoice = (index: number) =>
    onChange({ ...claim, choices: choices.filter((_, choiceIndex) => choiceIndex !== index) });

  return (
    <div>
      {choices.map((choice, index) => (
        <div key={index} className="field-grid">
          <span>Choice timing</span>
          <TimingField value={choice.timing} onChange={(timing) => setChoice(index, { ...choice, timing })} />
          <span>Chosen player</span>
          <PlayerSelect
            players={doc.players}
            value={choice.player}
            onChange={(player) => setChoice(index, { ...choice, player })}
          />
          <span>Died</span>
          <input
            type="checkbox"
            checked={choice.died}
            onChange={(event) => setChoice(index, { ...choice, died: event.target.checked })}
          />
          <span />
          <button type="button" onClick={() => removeChoice(index)}>
            Remove choice
          </button>
        </div>
      ))}
      <button type="button" onClick={addChoice}>
        + Add choice
      </button>
    </div>
  );
}

function InvestigatorBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: InvestigatorClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Minion role</span>
      <RoleSelect
        script={doc.script}
        value={claim.role ?? claim.minionRole}
        onChange={(v) => onChange({ ...claim, role: v || undefined, minionRole: undefined })}
        allowEmpty
        options={roleOptionsByCharacterType(doc.script, [CharacterType.Minion])}
        ariaLabel="Investigator minion role"
      />
      <span>Among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.among}
        onChange={(v) => onChange({ ...claim, among: v })}
        maxSelections={2}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function LibrarianBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: LibrarianClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Role</span>
      <RoleSelect
        script={doc.script}
        value={claim.role}
        onChange={(v) => onChange({ ...claim, role: v || undefined, outsiderCount: undefined })}
        allowEmpty
        options={roleOptionsByCharacterType(doc.script, [CharacterType.Outsider])}
        ariaLabel="Librarian outsider role"
      />
      <span>No Outsiders</span>
      <input
        type="checkbox"
        checked={claim.outsiderCount === 0}
        onChange={(event) => onChange({ ...claim, outsiderCount: event.target.checked ? 0 : undefined })}
      />
      <span>Among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.among ?? []}
        onChange={(v) => onChange({ ...claim, among: v })}
        maxSelections={2}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function WasherwomanBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: WasherwomanClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Role</span>
      <RoleSelect
        script={doc.script}
        value={claim.role}
        onChange={(v) => onChange({ ...claim, role: v || undefined })}
        allowEmpty
        options={roleOptionsByCharacterType(doc.script, [CharacterType.Townsfolk])}
        ariaLabel="Washerwoman townsfolk role"
      />
      <span>Among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.among}
        onChange={(v) => onChange({ ...claim, among: v })}
        maxSelections={2}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function ChambermaidBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: Extract<Claim, { readonly type: "Chambermaid" }>;
  onChange: (c: Claim) => void;
}) {
  const checks = claim.checks ?? [];
  const setCheck = (index: number, check: ChambermaidCheckDoc) =>
    onChange({ ...claim, checks: checks.map((entry, i) => (i === index ? check : entry)) });
  const addCheck = () =>
    onChange({
      ...claim,
      checks: [...checks, { left: doc.players[0] ?? "", right: doc.players[1] ?? "", count: 0 }],
    });
  const removeCheck = (index: number) =>
    onChange({ ...claim, checks: checks.filter((_, checkIndex) => checkIndex !== index) });

  return (
    <div>
      {checks.map((check, index) => (
        <div key={index} className="field-grid">
          <span>Left</span>
          <PlayerSelect
            players={doc.players}
            value={check.left}
            onChange={(left) => setCheck(index, { ...check, left })}
          />
          <span>Right</span>
          <PlayerSelect
            players={doc.players}
            value={check.right}
            onChange={(right) => setCheck(index, { ...check, right })}
          />
          <span>Count</span>
          <input
            type="number"
            min={0}
            value={check.count}
            onChange={(event) => setCheck(index, { ...check, count: Number(event.target.value) })}
          />
          <span>Timing</span>
          <TimingField value={check.timing} onChange={(timing) => setCheck(index, { ...check, timing })} />
          <span />
          <button type="button" onClick={() => removeCheck(index)}>
            Remove check
          </button>
        </div>
      ))}
      <button type="button" onClick={addCheck}>
        + Add check
      </button>
    </div>
  );
}

function ChefBody({ claim, onChange }: { claim: ChefClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Count</span>
      <input
        type="number"
        value={claim.count ?? ""}
        onChange={(e) => onChange({ ...claim, count: e.target.value === "" ? undefined : Number(e.target.value) })}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function EmpathBody({ claim, onChange }: { doc: PuzzleDoc; claim: EmpathClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Count</span>
      <input
        type="number"
        value={claim.count ?? ""}
        onChange={(e) => onChange({ ...claim, count: e.target.value === "" ? undefined : Number(e.target.value) })}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function FlowergirlBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: FlowergirlClaim;
  onChange: (c: Claim) => void;
}) {
  const votes = claim.votes ?? [];
  const setVote = (index: number, vote: FlowergirlVoteDoc) =>
    onChange({ ...claim, votes: votes.map((entry, voteIndex) => (voteIndex === index ? vote : entry)) });
  const addVote = () => onChange({ ...claim, votes: [...votes, { timing: "day_1", voters: [], demonVoted: false }] });
  const removeVote = (index: number) =>
    onChange({ ...claim, votes: votes.filter((_, voteIndex) => voteIndex !== index) });

  return (
    <div>
      {votes.map((vote, index) => (
        <div key={index} className="field-grid">
          <span>Vote timing</span>
          <TimingField
            value={vote.timing}
            onChange={(timing) => setVote(index, { ...vote, timing: timing ?? "day_1" })}
          />
          <span>Voters</span>
          <MultiPlayerSelect
            players={doc.players}
            value={vote.voters}
            onChange={(voters) => setVote(index, { ...vote, voters })}
          />
          <span>Demon voted</span>
          <OptionalBooleanSelect
            value={vote.demonVoted}
            onChange={(demonVoted) => setVote(index, { ...vote, demonVoted: demonVoted ?? false })}
          />
          <span />
          <button type="button" onClick={() => removeVote(index)}>
            Remove vote
          </button>
        </div>
      ))}
      <button type="button" onClick={addVote}>
        + Add vote
      </button>
    </div>
  );
}

function ExorcistBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: ExorcistClaim;
  onChange: (c: Claim) => void;
}) {
  const choices = claim.choices ?? [];
  const setChoice = (index: number, choice: ExorcistChoiceDoc) =>
    onChange({ ...claim, choices: choices.map((entry, choiceIndex) => (choiceIndex === index ? choice : entry)) });
  const addChoice = () => onChange({ ...claim, choices: [...choices, { player: doc.players[0] ?? "" }] });
  const removeChoice = (index: number) =>
    onChange({ ...claim, choices: choices.filter((_, choiceIndex) => choiceIndex !== index) });

  return (
    <div>
      {choices.map((choice, index) => (
        <div key={index} className="field-grid">
          <span>Choice timing</span>
          <TimingField
            value={choice.timing}
            onChange={(timing) => setChoice(index, { ...choice, timing })}
            defaultValue="night_2"
          />
          <span>Chosen player</span>
          <PlayerSelect
            players={doc.players}
            value={choice.player}
            onChange={(player) => setChoice(index, { ...choice, player })}
          />
          <span />
          <button type="button" onClick={() => removeChoice(index)}>
            Remove choice
          </button>
        </div>
      ))}
      <button type="button" onClick={addChoice}>
        + Add choice
      </button>
    </div>
  );
}

function FortuneTellerBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: FortuneTellerClaim;
  onChange: (c: Claim) => void;
}) {
  const check = claim.checks[0] ?? { left: "", right: "", yes: false };
  const setCheck = (next: FortuneTellerCheckDoc) => onChange({ ...claim, checks: [next] });

  return (
    <div className="field-grid">
      <span>Left</span>
      <PlayerSelect players={doc.players} value={check.left} onChange={(v) => setCheck({ ...check, left: v })} />
      <span>Right</span>
      <PlayerSelect players={doc.players} value={check.right} onChange={(v) => setCheck({ ...check, right: v })} />
      <span>Saw demon</span>
      <input type="checkbox" checked={check.yes} onChange={(e) => setCheck({ ...check, yes: e.target.checked })} />
      <span>Timing</span>
      <TimingField value={check.timing} onChange={(t) => setCheck({ ...check, timing: t })} />
    </div>
  );
}

function UndertakerBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: UndertakerClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Executed player</span>
      <PlayerSelect
        players={doc.players}
        value={claim.player}
        onChange={(v) => onChange({ ...claim, player: v || undefined })}
      />
      <span>Role learned</span>
      <RoleSelect
        script={doc.script}
        value={claim.role}
        onChange={(v) => onChange({ ...claim, role: v || undefined })}
        allowEmpty
        ariaLabel="Undertaker learned role"
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} defaultValue="night_2" />
    </div>
  );
}

function LegionaryBody({ claim, onChange }: { claim: LegionaryClaim; onChange: (c: Claim) => void }) {
  const counts = claim.counts ?? [];
  const setCount = (index: number, count: LegionaryCountDoc) =>
    onChange({ ...claim, counts: counts.map((entry, i) => (i === index ? count : entry)) });
  const addCount = () => onChange({ ...claim, counts: [...counts, { count: 0 }] });
  const removeCount = (index: number) =>
    onChange({ ...claim, counts: counts.filter((_, countIndex) => countIndex !== index) });

  return (
    <div>
      {counts.map((entry, index) => (
        <div key={index} className="field-grid">
          <span>Living evil</span>
          <input
            type="number"
            min={0}
            value={entry.count}
            onChange={(event) => setCount(index, { ...entry, count: Number(event.target.value) })}
          />
          <span>Timing</span>
          <TimingField value={entry.timing} onChange={(timing) => setCount(index, { ...entry, timing })} />
          <span />
          <button type="button" onClick={() => removeCount(index)}>
            Remove count
          </button>
        </div>
      ))}
      <button type="button" onClick={addCount}>
        + Add count
      </button>
    </div>
  );
}

function NobleBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: NobleClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>One evil among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.oneEvilAmong ?? []}
        onChange={(v) => onChange({ ...claim, oneEvilAmong: v })}
        maxSelections={3}
      />
    </div>
  );
}

function OracleBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: OracleClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Dead evil count</span>
      <input
        type="number"
        min={0}
        value={claim.count ?? ""}
        onChange={(event) =>
          onChange({ ...claim, count: event.target.value === "" ? undefined : Number(event.target.value) })
        }
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} />
    </div>
  );
}

function PhilosopherBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: PhilosopherClaim;
  onChange: (c: Claim) => void;
}) {
  const seamstress = claim.seamstress ?? { among: [doc.players[0] ?? "", doc.players[1] ?? ""], aligned: true };
  const setRole = (role: string) => {
    onChange({
      ...claim,
      role: role || undefined,
      seamstress: role === "Seamstress" ? seamstress : undefined,
    });
  };
  const setSeamstress = (next: NonNullable<PhilosopherClaim["seamstress"]>) => {
    onChange({ ...claim, seamstress: next });
  };

  return (
    <div className="field-grid">
      <span>Chosen role</span>
      <RoleSelect
        script={doc.script}
        value={claim.role}
        onChange={setRole}
        allowEmpty
        ariaLabel="Philosopher chosen role"
      />
      <span>Choice timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} />
      {claim.role === "Seamstress" && (
        <>
          <span>Seamstress left</span>
          <PlayerSelect
            players={doc.players}
            value={seamstress.among[0]}
            onChange={(left) => setSeamstress({ ...seamstress, among: [left, seamstress.among[1] ?? ""] })}
          />
          <span>Seamstress right</span>
          <PlayerSelect
            players={doc.players}
            value={seamstress.among[1]}
            onChange={(right) => setSeamstress({ ...seamstress, among: [seamstress.among[0] ?? "", right] })}
          />
          <span>Aligned</span>
          <input
            type="checkbox"
            checked={seamstress.aligned ?? false}
            onChange={(event) => setSeamstress({ ...seamstress, aligned: event.target.checked })}
          />
          <span>Info timing</span>
          <TimingField
            value={seamstress.timing ?? claim.timing}
            onChange={(timing) => setSeamstress({ ...seamstress, timing })}
          />
        </>
      )}
    </div>
  );
}

function PrincessBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: PrincessClaim;
  onChange: (c: Claim) => void;
}) {
  const nominations = claim.nominations ?? [];
  const setNomination = (index: number, nomination: PrincessNominationDoc) =>
    onChange({
      ...claim,
      nominations: nominations.map((entry, nominationIndex) => (nominationIndex === index ? nomination : entry)),
    });
  const addNomination = () =>
    onChange({ ...claim, nominations: [...nominations, { player: doc.players[0] ?? "", timing: "day_1" }] });
  const removeNomination = (index: number) =>
    onChange({ ...claim, nominations: nominations.filter((_, nominationIndex) => nominationIndex !== index) });

  return (
    <div>
      {nominations.map((nomination, index) => (
        <div key={index} className="field-grid">
          <span>Nomination timing</span>
          <TimingField
            value={nomination.timing}
            onChange={(timing) => setNomination(index, { ...nomination, timing })}
            defaultValue="day_1"
          />
          <span>Nominated player</span>
          <PlayerSelect
            players={doc.players}
            value={nomination.player}
            onChange={(player) => setNomination(index, { ...nomination, player })}
          />
          <span />
          <button type="button" onClick={() => removeNomination(index)}>
            Remove nomination
          </button>
        </div>
      ))}
      <button type="button" onClick={addNomination}>
        + Add nomination
      </button>
    </div>
  );
}

function ProdigyBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: ProdigyClaim; onChange: (c: Claim) => void }) {
  const setCheck = (index: number, check: ProdigyCheckDoc) =>
    onChange({ ...claim, checks: claim.checks.map((entry, checkIndex) => (checkIndex === index ? check : entry)) });
  const addCheck = () =>
    onChange({
      ...claim,
      checks: [...claim.checks, { chosen: doc.players[0] ?? "", learned: doc.players[1] ?? "" }],
    });
  const removeCheck = (index: number) =>
    onChange({ ...claim, checks: claim.checks.filter((_, checkIndex) => checkIndex !== index) });

  return (
    <div>
      {claim.checks.map((check, index) => (
        <div key={index} className="field-grid">
          <span>Check timing</span>
          <TimingField value={check.timing} onChange={(timing) => setCheck(index, { ...check, timing })} />
          <span>Chosen player</span>
          <PlayerSelect
            players={doc.players}
            value={check.chosen}
            onChange={(chosen) => setCheck(index, { ...check, chosen })}
          />
          <span>Learned player</span>
          <PlayerSelect
            players={doc.players}
            value={check.learned}
            onChange={(learned) => setCheck(index, { ...check, learned })}
          />
          <span />
          <button type="button" onClick={() => removeCheck(index)}>
            Remove check
          </button>
        </div>
      ))}
      <button type="button" onClick={addCheck}>
        + Add check
      </button>
    </div>
  );
}

function PuzzlemasterBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: PuzzlemasterClaim;
  onChange: (c: Claim) => void;
}) {
  const guesses = claim.guesses ?? [];
  const setGuess = (index: number, guess: PuzzlemasterGuessDoc) =>
    onChange({ ...claim, guesses: guesses.map((entry, guessIndex) => (guessIndex === index ? guess : entry)) });
  const addGuess = () =>
    onChange({
      ...claim,
      guesses: [...guesses, { player: doc.players[0] ?? "", learnedDemon: doc.players[1] ?? "", timing: "day_1" }],
    });
  const removeGuess = (index: number) =>
    onChange({ ...claim, guesses: guesses.filter((_, guessIndex) => guessIndex !== index) });

  return (
    <div>
      {guesses.map((guess, index) => (
        <div key={index} className="field-grid">
          <span>Guess timing</span>
          <TimingField value={guess.timing} onChange={(timing) => setGuess(index, { ...guess, timing })} />
          <span>Guessed drunk</span>
          <PlayerSelect
            players={doc.players}
            value={guess.player}
            onChange={(player) => setGuess(index, { ...guess, player })}
          />
          <span>Learned Demon</span>
          <PlayerSelect
            players={doc.players}
            value={guess.learnedDemon}
            onChange={(learnedDemon) => setGuess(index, { ...guess, learnedDemon })}
          />
          <span />
          <button type="button" onClick={() => removeGuess(index)}>
            Remove guess
          </button>
        </div>
      ))}
      <div className="field-grid">
        <span>Timing</span>
        <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} />
      </div>
      <button type="button" onClick={addGuess}>
        + Add guess
      </button>
    </div>
  );
}

function StewardBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: StewardClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Good player</span>
      <PlayerSelect
        players={doc.players}
        value={claim.goodPlayer}
        onChange={(v) => onChange({ ...claim, goodPlayer: v || undefined })}
      />
    </div>
  );
}

function KnightBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: KnightClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>No demon among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.noDemonAmong}
        onChange={(v) => onChange({ ...claim, noDemonAmong: v })}
        maxSelections={2}
      />
    </div>
  );
}

function SeamstressBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: SeamstressClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Left</span>
      <PlayerSelect
        players={doc.players}
        value={claim.among[0]}
        onChange={(v) => onChange({ ...claim, among: [v, claim.among[1] ?? ""] })}
      />
      <span>Right</span>
      <PlayerSelect
        players={doc.players}
        value={claim.among[1]}
        onChange={(v) => onChange({ ...claim, among: [claim.among[0] ?? "", v] })}
      />
      <span>Same alignment</span>
      <select
        value={claim.aligned === undefined ? "" : claim.aligned ? "same" : "different"}
        onChange={(e) =>
          onChange({
            ...claim,
            aligned: e.target.value === "" ? undefined : e.target.value === "same",
          })
        }
      >
        <option value="">-</option>
        <option value="same">same</option>
        <option value="different">different</option>
      </select>
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function JugglerBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: JugglerClaim; onChange: (c: Claim) => void }) {
  const setGuess = (player: string, role: string) => {
    const next = { ...claim.guesses, [player]: role };
    if (!role) delete next[player];
    onChange({ ...claim, guesses: next });
  };
  return (
    <div className="field-grid">
      <span>Correct count</span>
      <input
        type="number"
        value={claim.correctCount ?? ""}
        onChange={(e) =>
          onChange({ ...claim, correctCount: e.target.value === "" ? undefined : Number(e.target.value) })
        }
      />
      <span className="juggler-guesses-heading">Guesses</span>
      <div className="juggler-guesses">
        {doc.players.map((p) => (
          <Fragment key={p}>
            <span className="juggler-guess-player">{p}</span>
            <RoleSelect
              script={doc.script}
              value={claim.guesses[p]}
              onChange={(v) => setGuess(p, v)}
              allowEmpty
              options={sortedRoleNames(jugglerGuessRoleOptions(doc, p))}
              ariaLabel={`${p} Juggler guessed role`}
            />
          </Fragment>
        ))}
      </div>
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} defaultValue="night_2" />
    </div>
  );
}

function DreamerBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: DreamerClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Player checked</span>
      <PlayerSelect players={doc.players} value={claim.player} onChange={(v) => onChange({ ...claim, player: v })} />
      <span>Possible roles</span>
      <RoleListEditor
        value={claim.roles}
        onChange={(roles) => onChange({ ...claim, roles })}
        options={roleOptionsForScript(doc.script)}
        label="Dreamer possible roles"
        maxSelections={2}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function ShugenjaBody({ claim, onChange }: { claim: ShugenjaClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Evil direction</span>
      <select
        value={claim.evilDirection ?? "clockwise"}
        onChange={(e) => onChange({ ...claim, evilDirection: e.target.value as ShugenjaClaim["evilDirection"] })}
      >
        <option value="clockwise">clockwise</option>
        <option value="anticlockwise">anticlockwise</option>
      </select>
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function ClockmakerBody({ claim, onChange }: { doc: PuzzleDoc; claim: ClockmakerClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Demon-minion distance</span>
      <input
        type="number"
        min={1}
        value={claim.distance ?? ""}
        onChange={(e) => onChange({ ...claim, distance: e.target.value === "" ? undefined : Number(e.target.value) })}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function CourtierBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: CourtierClaim;
  onChange: (c: Claim) => void;
}) {
  const drunkTimings = claim.drunkTimings ?? [];
  const setTiming = (index: number, timing: string) => {
    onChange({ ...claim, drunkTimings: drunkTimings.map((entry, i) => (i === index ? timing : entry)) });
  };
  const removeTiming = (index: number) => {
    onChange({ ...claim, drunkTimings: drunkTimings.filter((_, i) => i !== index) });
  };
  const addTiming = () => {
    onChange({ ...claim, drunkTimings: [...drunkTimings, `night_${drunkTimings.length + 1}`] });
  };
  return (
    <div>
      <div className="field-grid">
        <span>Chosen role</span>
        <RoleSelect
          script={doc.script}
          value={claim.role}
          onChange={(role) => onChange({ ...claim, role: role || undefined })}
          allowEmpty
          ariaLabel="Courtier chosen role"
        />
        <span>Choice timing</span>
        <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} />
      </div>
      {drunkTimings.map((timing, index) => (
        <div key={index} className="field-grid">
          <span>Drunk timing</span>
          <TimingField value={timing} onChange={(nextTiming) => setTiming(index, nextTiming ?? "night_1")} />
          <span />
          <button type="button" onClick={() => removeTiming(index)}>
            Remove timing
          </button>
        </div>
      ))}
      <button type="button" onClick={addTiming}>
        + Add timing
      </button>
    </div>
  );
}

function MathematicianBody({ claim, onChange }: { claim: MathematicianClaim; onChange: (c: Claim) => void }) {
  const counts = claim.malfunctions ?? [];
  const setCount = (index: number, next: (typeof counts)[number]) => {
    onChange({ ...claim, malfunctions: counts.map((entry, i) => (i === index ? next : entry)) });
  };
  const removeCount = (index: number) => {
    onChange({ ...claim, malfunctions: counts.filter((_, i) => i !== index) });
  };
  const addCount = () => {
    onChange({ ...claim, malfunctions: [...counts, { timing: `night_${counts.length + 1}`, count: 0 }] });
  };
  return (
    <div>
      {counts.map((entry, index) => (
        <div key={index} className="field-grid">
          <span>Timing</span>
          <TimingField
            value={entry.timing}
            onChange={(timing) => setCount(index, { ...entry, timing: timing ?? "night_1" })}
          />
          <span>Malfunctions</span>
          <input
            type="number"
            min={0}
            value={entry.count}
            onChange={(event) => setCount(index, { ...entry, count: Number(event.target.value) })}
          />
          <span />
          <button type="button" onClick={() => removeCount(index)}>
            Remove count
          </button>
        </div>
      ))}
      <button type="button" onClick={addCount}>
        + Add count
      </button>
    </div>
  );
}

function RavenkeeperBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: RavenkeeperClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Player seen</span>
      <PlayerSelect
        players={doc.players}
        value={claim.player}
        onChange={(player) => onChange({ ...claim, player: player || undefined })}
      />
      <span>Role seen</span>
      <RoleSelect
        script={doc.script}
        value={claim.role}
        onChange={(role) => onChange({ ...claim, role: role || undefined })}
        allowEmpty
        ariaLabel="Ravenkeeper seen role"
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} defaultValue="night_2" />
    </div>
  );
}

function SageBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: SageClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Demon among</span>
      <MultiPlayerSelect
        players={doc.players}
        value={claim.demonAmong ?? []}
        maxSelections={2}
        onChange={(demonAmong) => onChange({ ...claim, demonAmong })}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
    </div>
  );
}

function SlayerBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: SlayerClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Shot player</span>
      <PlayerSelect
        players={doc.players}
        value={claim.target}
        onChange={(target) => onChange({ ...claim, target: target || undefined })}
      />
      <span>Shot timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} defaultValue="day_1" />
      <span>Target died</span>
      <select
        value={claim.killed === undefined ? "" : claim.killed ? "yes" : "no"}
        onChange={(event) => {
          const killed = event.target.value === "" ? undefined : event.target.value === "yes";
          onChange({ ...claim, killed, gameContinued: undefined });
        }}
      >
        <option value="">-</option>
        <option value="yes">yes</option>
        <option value="no">no</option>
      </select>
    </div>
  );
}

function SnakeCharmerBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: SnakeCharmerClaim;
  onChange: (c: Claim) => void;
}) {
  const check = claim.checks[0] ?? { player: "", demon: false, timing: "night_1" };
  const setCheck = (next: (typeof claim.checks)[number]) => onChange({ ...claim, checks: [next] });
  const setEvilTwin = (player: string) => {
    onChange({
      ...claim,
      evilTwin: player === "" ? undefined : { player, timing: claim.evilTwin?.timing ?? check.timing },
    });
  };
  const setEvilTwinTiming = (timing: string | undefined) => {
    const evilTwin = claim.evilTwin;
    if (evilTwin === undefined) return;
    onChange({ ...claim, evilTwin: { ...evilTwin, timing: timing ?? check.timing } });
  };

  return (
    <div className="field-grid">
      <span>Checked player</span>
      <PlayerSelect players={doc.players} value={check.player} onChange={(player) => setCheck({ ...check, player })} />
      <span>Is Demon</span>
      <select
        value={check.demon ? "yes" : "no"}
        onChange={(event) => setCheck({ ...check, demon: event.target.value === "yes" })}
      >
        <option value="yes">yes</option>
        <option value="no">no</option>
      </select>
      <span>Timing</span>
      <TimingField value={check.timing} onChange={(timing) => setCheck({ ...check, timing: timing ?? "night_1" })} />
      <span>Evil Twin</span>
      <PlayerSelect players={doc.players} value={claim.evilTwin?.player} onChange={setEvilTwin} />
      {claim.evilTwin !== undefined && (
        <>
          <span>Evil Twin timing</span>
          <TimingField value={claim.evilTwin.timing} onChange={setEvilTwinTiming} />
        </>
      )}
    </div>
  );
}

function VillageIdiotBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: VillageIdiotClaim;
  onChange: (c: Claim) => void;
}) {
  const radioGroupId = useId();
  const addCheck = () =>
    onChange({ ...claim, checks: [...claim.checks, { player: doc.players[0] ?? "", good: true }] });
  const setCheck = (i: number, c: (typeof claim.checks)[number]) =>
    onChange({ ...claim, checks: claim.checks.map((c0, j) => (j === i ? c : c0)) });
  const removeCheck = (i: number) => onChange({ ...claim, checks: claim.checks.filter((_, j) => j !== i) });
  return (
    <div>
      {claim.checks.map((chk, i) => (
        <div key={i} className="field-grid">
          <span>Timing</span>
          <TimingField value={chk.timing} onChange={(timing) => setCheck(i, { ...chk, timing })} />
          <span>Checked player</span>
          <PlayerSelect players={doc.players} value={chk.player} onChange={(v) => setCheck(i, { ...chk, player: v })} />
          <span>Registers as</span>
          <div className="radio-tile-group" role="radiogroup" aria-label="Registers as">
            <label className="radio-tile good">
              <input
                type="radio"
                name={`${radioGroupId}-check-${i}`}
                value="good"
                checked={chk.good}
                onChange={() => setCheck(i, { ...chk, good: true })}
              />
              <span>Good</span>
            </label>
            <label className="radio-tile evil">
              <input
                type="radio"
                name={`${radioGroupId}-check-${i}`}
                value="evil"
                checked={!chk.good}
                onChange={() => setCheck(i, { ...chk, good: false })}
              />
              <span>Evil</span>
            </label>
          </div>
          <span />
          <button type="button" onClick={() => removeCheck(i)}>
            Remove check
          </button>
        </div>
      ))}
      <button type="button" onClick={addCheck}>
        + Add check
      </button>
    </div>
  );
}

function KlutzBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: KlutzClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Chosen player</span>
      <PlayerSelect
        players={doc.players}
        value={claim.chosen}
        onChange={(chosen) => onChange({ ...claim, chosen: chosen || undefined })}
      />
      <span>Lost</span>
      <OptionalBooleanSelect value={claim.lost} onChange={(lost) => onChange({ ...claim, lost })} />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} defaultValue="day_1" />
    </div>
  );
}

function VirginBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: VirginClaim; onChange: (c: Claim) => void }) {
  return (
    <div className="field-grid">
      <span>Nominator</span>
      <PlayerSelect
        players={doc.players}
        value={claim.nominator}
        onChange={(nominator) => onChange({ ...claim, nominator: nominator || undefined })}
      />
      <span>Nominator executed</span>
      <OptionalBooleanSelect value={claim.executed} onChange={(executed) => onChange({ ...claim, executed })} />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} defaultValue="day_1" />
    </div>
  );
}

function BalloonistBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: BalloonistClaim;
  onChange: (c: Claim) => void;
}) {
  const addPair = () => {
    const first = doc.players[0] ?? "";
    const second = doc.players[1] ?? "";
    onChange({ ...claim, differentCharacterTypePairs: [...claim.differentCharacterTypePairs, [first, second]] });
  };
  const setPair = (i: number, p: readonly [string, string]) =>
    onChange({
      ...claim,
      differentCharacterTypePairs: claim.differentCharacterTypePairs.map((p0, j) => (j === i ? p : p0)),
    });
  const removePair = (i: number) =>
    onChange({
      ...claim,
      differentCharacterTypePairs: claim.differentCharacterTypePairs.filter((_, j) => j !== i),
    });
  return (
    <div>
      {claim.differentCharacterTypePairs.map((p, i) => (
        <div key={i} className="row">
          <PlayerSelect players={doc.players} value={p[0]} onChange={(v) => setPair(i, [v, p[1]])} />
          <span>→</span>
          <PlayerSelect players={doc.players} value={p[1]} onChange={(v) => setPair(i, [p[0], v])} />
          <button onClick={() => removePair(i)}>×</button>
        </div>
      ))}
      <button onClick={addPair}>+ Add pair</button>
      <div className="field-grid claim-footer-fields">
        <span>Timing</span>
        <TimingField
          value={claim.timing}
          onChange={(timing) => onChange({ ...claim, timing })}
          defaultValue="night_2"
        />
      </div>
    </div>
  );
}

function GamblerBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: Extract<Claim, { readonly type: "Gambler" }>;
  onChange: (c: Claim) => void;
}) {
  const guesses = claim.guesses ?? [];
  const setGuess = (index: number, guess: GamblerGuessDoc) =>
    onChange({ ...claim, guesses: guesses.map((entry, i) => (i === index ? guess : entry)) });
  const addGuess = () =>
    onChange({
      ...claim,
      guesses: [...guesses, { player: doc.players[0] ?? "", role: "" }],
    });
  const removeGuess = (index: number) =>
    onChange({ ...claim, guesses: guesses.filter((_, guessIndex) => guessIndex !== index) });

  return (
    <div>
      {guesses.map((guess, index) => (
        <div key={index} className="field-grid">
          <span>Player</span>
          <PlayerSelect
            players={doc.players}
            value={guess.player}
            onChange={(player) => setGuess(index, { ...guess, player })}
          />
          <span>Role</span>
          <RoleSelect
            script={doc.script}
            value={guess.role}
            onChange={(role) => setGuess(index, { ...guess, role })}
            allowEmpty
            ariaLabel="Gambler guessed role"
          />
          <span>Survived</span>
          <OptionalBooleanSelect
            value={guess.survived}
            onChange={(survived) => setGuess(index, { ...guess, survived })}
          />
          <span>Timing</span>
          <TimingField value={guess.timing} onChange={(timing) => setGuess(index, { ...guess, timing })} />
          <span />
          <button type="button" onClick={() => removeGuess(index)}>
            Remove guess
          </button>
        </div>
      ))}
      <button type="button" onClick={addGuess}>
        + Add guess
      </button>
    </div>
  );
}

function GossipBody({
  claim,
  onChange,
}: {
  claim: Extract<Claim, { readonly type: "Gossip" }>;
  onChange: (c: Claim) => void;
}) {
  const statements = claim.statements ?? [];
  const setStatement = (index: number, statement: GossipStatementDoc) =>
    onChange({ ...claim, statements: statements.map((entry, i) => (i === index ? statement : entry)) });
  const addStatement = () => onChange({ ...claim, statements: [...statements, { expression: "" }] });
  const removeStatement = (index: number) =>
    onChange({ ...claim, statements: statements.filter((_, statementIndex) => statementIndex !== index) });

  return (
    <div>
      {statements.map((statement, index) => {
        const expressionError = validateDslExpression(statement.expression);
        return (
          <div key={index} className="field-grid">
            <span>Timing</span>
            <TimingField
              value={statement.timing}
              onChange={(timing) => setStatement(index, { ...statement, timing })}
              defaultValue="day_1"
            />
            <span>Statement</span>
            <div>
              <textarea
                value={statement.expression}
                onChange={(event) => setStatement(index, { ...statement, expression: event.target.value })}
              />
              {expressionError && <div className="error">{expressionError}</div>}
            </div>
            <span />
            <button type="button" onClick={() => removeStatement(index)}>
              Remove statement
            </button>
          </div>
        );
      })}
      <button type="button" onClick={addStatement}>
        + Add statement
      </button>
    </div>
  );
}

function SavantBody({ doc, claim, onChange }: { doc: PuzzleDoc; claim: SavantClaim; onChange: (c: Claim) => void }) {
  void doc;
  const statement = claim.statements[0] ?? { options: ["", ""] };
  const setOptions = (options: readonly string[]) => onChange({ ...claim, statements: [{ options }] });
  const validate = (src: string): string | undefined => {
    if (!src.trim()) return "empty";
    try {
      parse(lex(src));
      return undefined;
    } catch (e) {
      if (e instanceof DslError) return `${e.message} (col ${e.span.start + 1})`;
      return e instanceof Error ? e.message : String(e);
    }
  };
  return (
    <div>
      <div className="field-grid">
        <span>Timing</span>
        <TimingField value={claim.timing} onChange={(t) => onChange({ ...claim, timing: t })} />
      </div>
      <div className="statement-block">
        <header className="row">
          <strong>Statement</strong>
          <span style={{ opacity: 0.6 }}>(exactly one option is true)</span>
        </header>
        {statement.options.map((opt, oi) => {
          const err = validate(opt);
          return (
            <div key={oi}>
              <textarea
                value={opt}
                onChange={(e) => {
                  const nextOptions = statement.options.map((o, j) => (j === oi ? e.target.value : o));
                  setOptions(nextOptions);
                }}
              />
              {err && err !== "empty" && <div className="error">{err}</div>}
              <button
                onClick={() => {
                  const nextOptions = statement.options.filter((_, j) => j !== oi);
                  setOptions(nextOptions);
                }}
              >
                Remove option
              </button>
            </div>
          );
        })}
        <button onClick={() => setOptions([...statement.options, ""])}>+ Add option</button>
      </div>
    </div>
  );
}

function NightwatchmanBody({
  doc,
  claim,
  onChange,
}: {
  doc: PuzzleDoc;
  claim: NightwatchmanClaim;
  onChange: (c: Claim) => void;
}) {
  return (
    <div className="field-grid">
      <span>Chosen player</span>
      <PlayerSelect
        players={doc.players}
        value={claim.chosen}
        onChange={(chosen) => onChange({ ...claim, chosen: chosen || undefined })}
      />
      <span>Learned</span>
      <OptionalBooleanSelect value={claim.learned} onChange={(learned) => onChange({ ...claim, learned })} />
      <span>Confirmed by chosen</span>
      <input
        type="checkbox"
        checked={claim.confirmedByChosen === true}
        onChange={(event) => onChange({ ...claim, confirmedByChosen: event.target.checked ? true : undefined })}
      />
      <span>Timing</span>
      <TimingField value={claim.timing} onChange={(timing) => onChange({ ...claim, timing })} />
    </div>
  );
}
