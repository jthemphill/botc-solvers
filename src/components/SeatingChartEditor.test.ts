import { describe, expect, test } from "bun:test";
import { claimSummary } from "./claimSummary";

describe("claimSummary", () => {
  test("summarizes Slayer no-kill shots with target and timing", () => {
    expect(claimSummary({ type: "Slayer", name: "Adam", timing: "day_3", target: "Matthew", killed: false })).toBe(
      "I shot Matthew on day 3 and nothing happened.",
    );
  });
});
