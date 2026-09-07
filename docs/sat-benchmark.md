# SAT benchmark — 2026-09-07

The optimized engine enumerates the same 140 initial role assignments across all 91 catalog puzzles. Total measured time falls by 14.3%, and SAT backend time falls by 26.2%. No puzzle data, solution fixtures, character rules, or enumeration limits changed.

## Method

- Machine: Apple M4, macOS arm64, Bun 1.3.14; bundled Kissat WebAssembly backend.
- Baseline engine: commit `93d1c522486cfe799318d2f4a4d70c0065ddf94d`. Optimized engine: the accompanying working-tree changes.
- Each measurement starts a fresh process, initializes Kissat once, runs one full catalog warmup, then runs seven full catalog passes sequentially. No tests or builds run concurrently with these measurements.
- Each puzzle uses a new model and exhaustive initial-character enumeration, including the final UNSAT call. The catalog includes the intro. All measurements completed.
- Each table entry is the median of seven samples. Aggregate times sum the per-puzzle medians; they are not the median of whole-pass times. Medians of separate phases do not necessarily add to the total median.
- Build time includes document validation and model construction. Finalization completes and freezes the constraints. Enumeration includes witness validation and decoding. Backend time is a subset of enumeration time and includes solver creation, clause loading, search, model extraction, and release.
- Runtime initialization, hashing, and report output are outside the measured puzzle times. Sorted initial role-assignment hashes match for every puzzle before and after. Hidden choices are not compared because equally valid witnesses can differ.
- Timings are specific to this machine. Existing character and interaction coverage remains incomplete; matching assignments does not establish complete game-rule support.

## Aggregate results

| Metric           |   Before |    After | Reduction |
| ---------------- | -------: | -------: | --------: |
| Build (ms)       |   494.21 |   478.32 |      3.2% |
| Finalize (ms)    |   524.75 |   425.99 |     18.8% |
| Enumeration (ms) |   350.71 |   268.36 |     23.5% |
| SAT backend (ms) |   268.73 |   198.32 |     26.2% |
| Total (ms)       | 1,374.31 | 1,178.47 |     14.3% |
| Variables        |  251,333 |  170,796 |     32.0% |
| Clauses          |  672,780 |  526,652 |     21.7% |

Before whole-pass measured totals (ms): 1371.4, 1381.7, 1388.0, 1364.9, 1389.7, 1382.8, 1379.6.

After whole-pass measured totals (ms): 1202.3, 1185.9, 1196.8, 1179.1, 1186.5, 1179.6, 1186.9.

## Changes and validation

1. Encode an all-but-one upper bound as one clause. This also makes an at-least-one constraint a single clause, removing a quadratic counter from each exactly-one selection.
2. Encode reified zero/all counts with one AND gate. For other high counts, count false inputs to reduce counter levels. Signed inputs and repeated occurrences retain their arithmetic meaning.
3. Freeze the already-owned clause arrays at finalization without copying every clause again. The input array is still copied when added, and returned snapshots remain frozen.

A CPU profile after the count changes attributed 24% of sampled time to `Object.freeze`; removing the extra copy is a small allocation reduction, not a removal of freezing. The count changes account for most of the measured improvement.

Validation: 407 unit tests pass, including all published puzzle role-assignment fixtures. Exhaustive arithmetic checks cover both reified truth values, signed and repeated literals, complementary literals, disabled constraints, and boundary counts. A snapshot test checks input isolation and runtime immutability. Typechecking, the production build, and the desktop/mobile browser solve-edit-reimport workflows pass. The build retains its bundle-size warning.

## Reproduce

```sh
bun run benchmark --runs 7 --output /tmp/botc-before.json
# Apply the engine changes, then compare:
bun run benchmark --runs 7 --compare /tmp/botc-before.json --output /tmp/botc-after.json
# Inspect one puzzle:
bun run benchmark --filter puzzle-82 --runs 7
```

The JSON reports retain all raw samples, per-puzzle medians, assignment hashes, environment details, and formula sizes. Comparison fails if a puzzle is missing or its assignments or completion status differ. The synthetic benchmark remains available as `bun scripts/benchmark-engine.ts`.

## Per-puzzle results

Times are milliseconds. SAT denotes backend time, which is included in total time.

| Puzzle                                            | Worlds | Total before | Total after | SAT before | SAT after | Variables before → after | Clauses before → after |
| ------------------------------------------------- | -----: | -----------: | ----------: | ---------: | --------: | -----------------------: | ---------------------: |
| intro                                             |     38 |        14.24 |       10.15 |       9.45 |      6.62 |                577 → 334 |            1423 → 1004 |
| puzzle-01-sober-savant                            |      1 |         2.64 |        2.16 |       0.54 |      0.39 |                806 → 545 |            1944 → 1485 |
| puzzle-02-come-fly-with-me                        |      1 |         4.90 |        3.69 |       1.41 |      1.06 |              1634 → 1026 |            3531 → 2437 |
| puzzle-03a-not-throwing-away-my-shot              |      1 |         4.45 |        3.11 |       1.41 |      0.94 |               1546 → 861 |            3356 → 2106 |
| puzzle-03b-not-throwing-away-my-shot              |      1 |         5.70 |        3.58 |       2.01 |      1.19 |              1943 → 1011 |            4167 → 2456 |
| puzzle-04-the-many-headed-monster                 |      2 |         7.68 |        5.58 |       2.39 |      1.57 |              2212 → 1359 |            4827 → 3287 |
| puzzle-05a-you-only-guess-twice                   |      2 |         1.86 |        1.28 |       0.58 |      0.37 |                676 → 382 |             1406 → 886 |
| puzzle-05b-you-only-guess-twice                   |      4 |         2.35 |        1.71 |       0.94 |      0.62 |                683 → 388 |             1417 → 895 |
| puzzle-06-super-marionette-bros                   |      1 |        45.52 |       42.77 |       6.39 |      3.92 |              3020 → 2056 |            9026 → 7247 |
| puzzle-07-the-savant-strikes-back                 |      1 |         5.72 |        4.57 |       1.07 |      0.75 |              1849 → 1267 |            4191 → 3140 |
| puzzle-08-the-stitch-up                           |      2 |         1.36 |        1.12 |       0.52 |      0.43 |                369 → 264 |              811 → 640 |
| puzzle-09-the-new-acrobat                         |      1 |         6.21 |        5.29 |       1.16 |      0.85 |              1945 → 1326 |            4489 → 3392 |
| puzzle-10-dont-overcook-it                        |      1 |         6.15 |        4.51 |       1.61 |      1.09 |              2067 → 1309 |            4606 → 3233 |
| puzzle-11-false-is-the-new-black                  |      1 |        49.12 |       39.23 |      14.36 |      9.54 |             10300 → 7180 |          29851 → 24259 |
| puzzle-12a-thunderstruck                          |      1 |         2.23 |        1.68 |       0.49 |      0.33 |                751 → 435 |            1806 → 1243 |
| puzzle-12b-thunderstruck                          |      1 |         3.72 |        2.48 |       0.92 |      0.59 |               1398 → 786 |            3095 → 1980 |
| puzzle-13-clockblocking                           |      1 |         6.68 |        4.86 |       1.90 |      1.32 |              2062 → 1304 |            4650 → 3277 |
| puzzle-14-new-super-marionette-bros               |      1 |         5.29 |        3.78 |       1.46 |      1.01 |              1800 → 1087 |            4047 → 2752 |
| puzzle-15-wake-up-and-choose-violets              |      1 |        20.20 |       19.27 |       1.97 |      1.64 |              2149 → 1618 |            6716 → 5748 |
| puzzle-16-who-watches-the-watchmen                |      1 |        10.00 |        7.67 |       2.71 |      1.94 |              3021 → 1947 |            6832 → 4875 |
| puzzle-17-the-missing-piece                       |      4 |        10.05 |        7.76 |       3.07 |      2.29 |              1984 → 1390 |            4456 → 3398 |
| puzzle-18-x-and-the-city                          |      1 |         7.60 |        5.87 |       2.34 |      1.60 |              2299 → 1634 |            5052 → 3857 |
| puzzle-19-he-could-be-you-he-could-be-me          |      1 |         7.68 |        5.27 |       2.32 |      1.41 |              2522 → 1518 |            5584 → 3749 |
| puzzle-20-the-three-wise-men                      |      1 |         4.59 |        3.47 |       1.34 |      1.03 |              1572 → 1002 |            3512 → 2495 |
| puzzle-21-eight-jugglers-juggling                 |      1 |         1.16 |        0.94 |       0.33 |      0.26 |                460 → 322 |              970 → 738 |
| puzzle-22-one-in-the-chamber                      |      1 |        10.85 |        8.62 |       2.92 |      1.99 |              3185 → 2110 |            7153 → 5193 |
| puzzle-23-goblincore                              |      1 |         4.02 |        3.04 |       0.82 |      0.53 |               1497 → 961 |            3307 → 2349 |
| puzzle-24-the-ultimate-blunder                    |      1 |         4.87 |        3.48 |       1.37 |      0.93 |              1701 → 1040 |            3806 → 2619 |
| puzzle-26-a-major-problem                         |      1 |        10.86 |        8.19 |       3.80 |      2.73 |              3012 → 1938 |            6802 → 4845 |
| puzzle-27-is-this-a-legion-game                   |      1 |         3.35 |        2.79 |       0.80 |      0.62 |               1094 → 811 |            2580 → 2106 |
| puzzle-28-a-study-in-scarlet                      |      1 |        27.35 |       25.49 |       5.25 |      5.55 |              3479 → 2597 |           10486 → 8905 |
| puzzle-29-a-dreamer-im-not-the-only-one           |      1 |         2.74 |        2.23 |       0.85 |      0.62 |                836 → 597 |            1917 → 1511 |
| puzzle-30-the-babel-fish-is-a-dead-giveaway-left  |      1 |         1.22 |        0.88 |       0.27 |      0.16 |                448 → 232 |             1106 → 722 |
| puzzle-30-the-babel-fish-is-a-dead-giveaway-right |      1 |         1.81 |        1.30 |       0.59 |      0.35 |                632 → 371 |            1559 → 1100 |
| puzzle-31-no-your-other-left                      |      1 |         8.70 |        6.70 |       2.99 |      2.03 |              2421 → 1637 |            5531 → 4115 |
| puzzle-32-prepare-for-juggle-and-make-it-double   |      1 |         8.24 |        6.32 |       2.56 |      1.70 |              2456 → 1636 |            5554 → 4088 |
| puzzle-33-twice-is-coincidence-thrice-is-proof    |      1 |         9.58 |        7.16 |       2.80 |      1.92 |              2919 → 1845 |            6549 → 4592 |
| puzzle-34-the-vortox-conjecture                   |      1 |        15.21 |       13.82 |       1.15 |      0.88 |               1334 → 946 |            3776 → 3082 |
| puzzle-35-typhon-season                           |      1 |         6.38 |        4.38 |       1.80 |      1.24 |              2108 → 1235 |            4758 → 3168 |
| puzzle-36-what-is-your-weapon-of-choice           |      1 |         9.76 |        7.53 |       2.33 |      1.69 |              3004 → 1979 |            6749 → 4896 |
| puzzle-37-new-super-marionette-bros-u             |      1 |         8.75 |        6.67 |       2.14 |      1.41 |              2693 → 1780 |            6200 → 4543 |
| puzzle-38-snakes-on-a-plane                       |      1 |         9.25 |        7.01 |       2.57 |      1.74 |              2805 → 1835 |            6380 → 4623 |
| puzzle-39-squid-game                              |      1 |        11.99 |       10.88 |       1.64 |      1.23 |              2088 → 1488 |            5961 → 4875 |
| puzzle-40-nine-lives                              |      1 |        15.42 |       11.97 |       5.29 |      4.09 |              3955 → 2564 |            8904 → 6347 |
| puzzle-41-no-john-you-are-the-demons              |      1 |         5.86 |        4.49 |       1.18 |      0.80 |              1923 → 1286 |            4320 → 3176 |
| puzzle-42-life-the-universe-and-everything        |      1 |         8.20 |        6.42 |       1.96 |      1.38 |              2543 → 1723 |            5859 → 4380 |
| puzzle-43-two-many-cooks                          |      1 |         8.89 |        7.01 |       2.19 |      1.68 |              2832 → 1862 |            6405 → 4648 |
| puzzle-44-trouble-homebrewing                     |      1 |         4.91 |        3.71 |       1.43 |      1.02 |              1620 → 1060 |            3587 → 2575 |
| puzzle-45a-dont-try-this-at-home                  |      1 |         9.93 |        8.01 |       2.25 |      1.63 |              2942 → 2005 |            6851 → 5133 |
| puzzle-45b-dont-try-this-at-home                  |      1 |         8.11 |        6.43 |       1.80 |      1.21 |              2610 → 1705 |            6025 → 4364 |
| puzzle-46-the-princess-diaries                    |      3 |         6.26 |        4.86 |       1.86 |      1.33 |              1470 → 1042 |            3336 → 2584 |
| puzzle-47-we-have-evil-twin-at-home               |      1 |        15.70 |       12.99 |       4.22 |      3.68 |              4031 → 2747 |            9181 → 6833 |
| puzzle-48-solving-for-x                           |      1 |         7.52 |        6.18 |       1.85 |      1.47 |              2446 → 1750 |            5323 → 4084 |
| puzzle-49-bastille-day                            |      1 |         6.70 |        5.02 |       2.00 |      1.43 |              2202 → 1421 |            4906 → 3495 |
| puzzle-51-weird-science                           |      1 |         4.91 |        3.11 |       1.12 |      0.64 |              1944 → 1054 |            4152 → 2535 |
| puzzle-52-two-votes-is-enough                     |      1 |        16.59 |       12.73 |       4.70 |      3.23 |              4272 → 2867 |            9727 → 7146 |
| puzzle-53-lets-do-the-time-warp-again             |      1 |        37.34 |       35.47 |       4.37 |      3.90 |              3753 → 2654 |           10930 → 8930 |
| puzzle-54-silence-in-the-library                  |      1 |         9.09 |        6.74 |       2.96 |      1.76 |              2548 → 1661 |            5774 → 4159 |
| puzzle-55-the-life-of-a-flowergirl                |      2 |        41.55 |       38.04 |       5.54 |      4.45 |              3681 → 2564 |           10524 → 8471 |
| puzzle-56-meanwhile-at-the-legion-of-doom         |      1 |         8.28 |        6.80 |       1.54 |      1.18 |              2387 → 1729 |            5517 → 4327 |
| puzzle-57-neither-victims-nor-executioners        |      1 |        10.64 |        7.57 |       2.33 |      1.48 |              3639 → 2216 |            7942 → 5432 |
| puzzle-58-minus-one-thats-three                   |      1 |        10.27 |        9.42 |       2.42 |      1.70 |              2741 → 2074 |            5986 → 4781 |
| puzzle-59-fifty-fifty                             |      1 |        15.80 |       12.20 |       4.03 |      2.64 |              4281 → 2871 |            9745 → 7154 |
| puzzle-60-whats-a-mind-goblin                     |      1 |        29.38 |       27.54 |       1.96 |      1.59 |              2405 → 1804 |            7464 → 6374 |
| puzzle-61-thus-with-a-kiss-i-die                  |      1 |        48.82 |       45.76 |       4.69 |      3.53 |              3961 → 2821 |           11752 → 9680 |
| puzzle-62-have-you-ever-seen-the-rain             |      1 |        12.69 |       10.59 |       2.80 |      2.00 |              3347 → 2366 |            7749 → 5958 |
| puzzle-63-the-limiting-factor                     |      1 |        17.83 |       12.70 |       4.47 |      3.05 |              4356 → 2913 |            9936 → 7285 |
| puzzle-64-copycatholic                            |      1 |        15.85 |       13.23 |       3.33 |      2.61 |              4160 → 2927 |            9446 → 7271 |
| puzzle-65-the-slip-up                             |      1 |        37.00 |       33.93 |       3.30 |      2.67 |              3232 → 2372 |            9572 → 8007 |
| puzzle-66-the-useful-idiot                        |      1 |         4.80 |        3.80 |       1.23 |      0.92 |              1399 → 1013 |            3170 → 2508 |
| puzzle-67-minus-one-thats-three-times-two         |      1 |        12.45 |       10.16 |       4.04 |      2.83 |              2851 → 2184 |            6218 → 5013 |
| puzzle-68-the-numbers-are-all-wrong               |      1 |         5.73 |        4.50 |       1.12 |      0.77 |              1930 → 1316 |            4256 → 3147 |
| puzzle-69-thats-the-sects-number                  |      1 |        59.50 |       56.81 |       4.86 |      3.86 |              5014 → 3601 |          14716 → 12121 |
| puzzle-70-digging-your-own-grave                  |      1 |        16.21 |       12.47 |       3.75 |      2.54 |              4334 → 2894 |            9872 → 7229 |
| puzzle-71-the-disappearing-act                    |      1 |        37.61 |       35.54 |       2.60 |      2.02 |              2673 → 2002 |            8119 → 6917 |
| puzzle-72-one-digit-too-many                      |      1 |         6.09 |        4.88 |       1.28 |      0.94 |              1892 → 1297 |            4403 → 3305 |
| puzzle-73-opening-theory                          |      1 |        10.36 |        8.55 |       2.33 |      1.56 |              2812 → 1974 |            6627 → 5120 |
| puzzle-74-youre-obviously-evil                    |      1 |        16.61 |       12.20 |       3.71 |      2.31 |              4347 → 2900 |            9868 → 7211 |
| puzzle-75-cut-from-the-same-cloth                 |      1 |        42.12 |       38.85 |       4.11 |      3.11 |              3657 → 2555 |           10426 → 8419 |
| puzzle-76-three-for-three                         |      1 |        11.06 |        6.28 |       2.64 |      1.30 |              4352 → 1937 |            9588 → 5014 |
| puzzle-77-yes-but-dont                            |      1 |        15.44 |       12.80 |       3.04 |      2.12 |              4320 → 2909 |            9851 → 7258 |
| puzzle-78-its-pronounced-eefa                     |      1 |        19.18 |       15.48 |       4.76 |      3.25 |              4725 → 3251 |           10795 → 8092 |
| puzzle-79-erudition-lesson                        |      1 |        48.41 |       45.44 |       4.85 |      3.54 |              4487 → 3350 |          13708 → 11629 |
| puzzle-80-the-x-factor                            |      1 |        21.43 |       19.59 |       4.22 |      3.27 |              4511 → 3334 |           10330 → 8172 |
| puzzle-81-arachnophobia                           |      1 |        16.38 |       12.69 |       4.50 |      2.87 |              4134 → 2796 |            9419 → 6956 |
| puzzle-82-shoot-the-messenger                     |      1 |        63.63 |       59.27 |       7.43 |      5.66 |              4999 → 3441 |          14547 → 11673 |
| puzzle-83-be-the-one                              |      1 |         8.00 |        5.92 |       2.66 |      1.58 |              2111 → 1407 |            4895 → 3633 |
| puzzle-84-mech4an4ion-is-inver10d                 |      1 |         4.62 |        3.51 |       1.00 |      0.68 |              1661 → 1063 |            3602 → 2538 |
| puzzle-85-trust-is-a-two-way-street               |      1 |        16.76 |       13.49 |       4.32 |      3.18 |              4362 → 2916 |            9902 → 7247 |
| puzzle-86-blood-and-ink                           |      1 |        18.06 |       15.37 |       2.35 |      1.74 |              2619 → 1775 |            7281 → 5814 |
| a-clean-sweep                                     |      1 |       114.30 |      109.64 |      23.01 |     22.03 |             11505 → 9434 |          88335 → 84596 |
