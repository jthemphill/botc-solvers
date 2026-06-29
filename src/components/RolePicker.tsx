import { useEffect, useId, useMemo, useState, type KeyboardEvent } from "react";
import { roleEmojiLabel } from "../model/roleEmoji";
import { canonicalRoleName } from "../state/scriptRoles";

export function sortedRoleNames(roles: readonly string[]): string[] {
  return [...new Set(roles)].sort((left, right) => left.localeCompare(right));
}

function roleOptionsWithValue(options: readonly string[], value: string | undefined): string[] {
  const canonicalValue = canonicalRoleName(value);
  return sortedRoleNames(canonicalValue === undefined ? options : [canonicalValue, ...options]);
}

export function RoleTypeahead({
  value,
  onChange,
  options,
  allowEmpty = false,
  ariaLabel = "Role",
  placeholder = "Role",
}: {
  value: string | undefined;
  onChange: (value: string) => void;
  options: readonly string[];
  allowEmpty?: boolean;
  ariaLabel?: string;
  placeholder?: string;
}) {
  const listId = useId();
  const roleOptions = useMemo(() => roleOptionsWithValue(options, value), [options, value]);
  const optionSet = useMemo(() => new Set(roleOptions), [roleOptions]);
  const [draft, setDraft] = useState(value ?? "");

  useEffect(() => setDraft(value ?? ""), [value]);

  const commit = (rawValue = draft) => {
    const trimmed = rawValue.trim();
    if (trimmed === "") {
      if (allowEmpty) {
        setDraft("");
        if ((value ?? "") !== "") onChange("");
      } else {
        setDraft(value ?? "");
      }
      return;
    }

    const canonical = canonicalRoleName(trimmed);
    if (canonical !== undefined && optionSet.has(canonical)) {
      setDraft(canonical);
      if (canonical !== value) onChange(canonical);
      return;
    }

    setDraft(value ?? "");
  };

  const pickFirstMatchingRole = () => {
    const normalizedDraft = draft.trim().toLowerCase();
    if (normalizedDraft === "") return undefined;
    return roleOptions.find((role) => role.toLowerCase().includes(normalizedDraft));
  };

  const handleKeyDown = (event: KeyboardEvent<HTMLInputElement>) => {
    if (event.key !== "Enter") return;
    event.preventDefault();
    commit(pickFirstMatchingRole() ?? draft);
  };

  return (
    <>
      <input
        type="text"
        list={listId}
        value={draft}
        onChange={(event) => {
          const nextDraft = event.target.value;
          setDraft(nextDraft);
          const canonical = canonicalRoleName(nextDraft);
          if (canonical !== undefined && optionSet.has(canonical)) onChange(canonical);
          if (allowEmpty && nextDraft === "") onChange("");
        }}
        onBlur={() => commit()}
        onKeyDown={handleKeyDown}
        aria-label={ariaLabel}
        placeholder={placeholder}
      />
      <datalist id={listId}>
        {roleOptions.map((role) => (
          <option key={role} value={role}>
            {roleEmojiLabel(role)}
          </option>
        ))}
      </datalist>
    </>
  );
}

export function RoleListEditor({
  value,
  onChange,
  options,
  label,
  maxSelections,
}: {
  value: readonly string[];
  onChange: (value: readonly string[]) => void;
  options: readonly string[];
  label: string;
  maxSelections?: number;
}) {
  const [addKey, setAddKey] = useState(0);
  const selected = sortedRoleNames(value);
  const selectedSet = new Set(selected);
  const availableOptions = sortedRoleNames(options.filter((role) => !selectedSet.has(role)));
  const atLimit = maxSelections !== undefined && selected.length >= maxSelections;

  const addRole = (role: string) => {
    if (role === "" || selectedSet.has(role) || atLimit) return;
    onChange([...selected, role]);
    setAddKey((key) => key + 1);
  };

  const removeRole = (role: string) => {
    onChange(selected.filter((entry) => entry !== role));
  };

  return (
    <div className="role-list-editor">
      <div className="role-chip-list" aria-label={label}>
        {selected.map((role) => (
          <button key={role} type="button" className="role-chip" onClick={() => removeRole(role)}>
            {roleEmojiLabel(role)}
            <span aria-hidden="true">×</span>
          </button>
        ))}
        {selected.length === 0 && <span className="role-chip-empty">No roles selected.</span>}
      </div>
      {!atLimit && (
        <RoleTypeahead
          key={addKey}
          value=""
          onChange={addRole}
          options={availableOptions}
          allowEmpty
          ariaLabel={`Add ${label}`}
          placeholder="Add role"
        />
      )}
    </div>
  );
}
