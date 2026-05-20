# Model Decisions

## Puzzle 5a: You Only Guess Twice

- Added `Alsaahir` as a role class with Townsfolk metadata only. The Alsaahir ability is not modeled as a normal information claim because puzzle 5a asks for a public guess after solving the current worlds, not for a constraint that changes the pre-guess world set.
- Represented the Alsaahir guess as puzzle-specific post-processing in `possibleAlsaahirGuesses`. This keeps the core SAT model focused on legal worlds and lets the puzzle describe the decision policy: guess one candidate evil team; if the guess is wrong, the only remaining candidate is the answer.
- Modeled "no Outsiders in play" by including `Drunk` in the script with count `0`. This preserves the existing claim helper behavior for Townsfolk, which allows a claimed Townsfolk token to be an actual Drunk when the script permits it.

## Puzzle 5b: You Only Guess Twice

- Kept the Juggler's unused ability out of the SAT model for the same reason as Alsaahir: the legal worlds are determined before the public action, and the action is a decision tree over those worlds.
- Added `possibleJuggles` as puzzle-specific post-processing. It searches three public Juggler guesses and keeps plans where each possible count maps to exactly one demon/minion assignment.

## Puzzle 6: Super Marionette Bros

- Added `Pukka`, `No Dashii`, and `Vortox` as Demon role classes with metadata only. Their puzzle-specific mechanical effects are still encoded in the puzzle file because the existing role classes model information claims, not full night/action timing.
- Added `BOTCModel.allowPoisonInContext` so a puzzle can define its own poison source constraints without the model's default sober fallback forcing that context to false.
- Modeled Vortox as false information only for an actual, sober/healthy Townsfolk claim. Drunk, poisoned, Demon, and Marionette cases remain unconstrained because their shown information may be arbitrary.
- Modeled the Marionette as neighboring the Demon, but did not make Marionette information true. If the Marionette saw a Townsfolk token, that explains the role report but does not constrain the factual content of the information.
- Used the death record as a demon constraint: Fraser and Steph cannot be the Demon, and if the Demon is Pukka then Steph was the night-one poisoned player who died on night two.

## Puzzle 7: The Savant Strikes Back

- Added `Mutant`, `Shugenja`, and `Village Idiot` role classes. `Mutant` is metadata only; `Shugenja` and `Village Idiot` include their information predicates.
- Extended `addRoleClaim` with `extraPossibleActualRoles` so puzzle-specific madness cases can allow a non-Drunk good role to claim a Townsfolk token while keeping its information unconstrained.
- Disabled global role uniqueness only for puzzle 7, then re-applied at-most-one constraints to every role except `Village Idiot`. This models the Village Idiot setup without weakening uniqueness for the rest of the script.
- Modeled Fortune Teller red herring and the drunk extra Village Idiot locally in the puzzle file. They are setup state for this puzzle's statements, not general player roles.

## Puzzle 8: The Stitch-Up

- Reused the duplicate-role pattern for the Bootlegger rule "Every Townsfolk is a Seamstress": puzzle 8 disables global uniqueness and uses a script containing only `Seamstress` for Townsfolk.
- Used the existing `addPoisonerEffect` for night-one poisoning. The puzzle resolves the evil team, but not which evil player is the Imp versus the Poisoner.

## Puzzle 9: The New Acrobat

- Added `Po`, `Acrobat`, `Gambler`, and `Gossip` role classes with metadata only. Their death-trigger behavior is encoded in puzzle 9 because it depends on the public death timeline.
- Modeled the new Acrobat as a Townsfolk whose choices constrain Drunk status only when You are actually the Acrobat. If You is the Drunk, the claimed Acrobat ability is not trusted.
- Kept the SAT role assignment as the starting role assignment and added puzzle-local event constraints for night three: the Imp self-kills/starpasses, You dies from choosing the Drunk with Acrobat, and Oscar's true day-two Gossip statement accounts for the remaining death.
- Modeled the Po timing correction explicitly: if a Po is responsible for three night-three deaths, it must have charged on night two, so the night-two death would need to be Oscar's true day-one Gossip statement that Fraser was the Demon. This eliminates the static Po worlds.
- Puzzle 9 now resolves as Anna starting as the Imp and Hannah starting as the Goblin; Anna starpasses to Hannah on night three.

## Puzzle 10: Don't Overcook It

- Added `Ravenkeeper` as a Townsfolk role class with metadata only; the death-triggered information is encoded directly in puzzle 10 because it refers to Matthew's specific death.
- Reused Poisoner contexts to separate night-one setup information from night-two/day-two information after Josh was executed. If Josh is the Poisoner, night-two poisoning is inactive.
- Modeled Fortune Teller red herring locally again. The red herring is setup state tied to a Fortune Teller being in play, not a role assignment.

## Puzzle 11: False Is the New Black

- Added metadata classes for `Cerenovus`, `Pit-Hag`, `Sweetheart`, `Artist`, `Philosopher`, `Sage`, and `Snake Charmer`.
- Kept the Vortox false-info logic puzzle-local. Puzzle 11 has several role-change and madness claims, so the file models which reported facts are reliable rather than changing the base claim helper.
- Represented Mutant madness by allowing live Townsfolk claims to be actual `Mutant` with arbitrary information. Dead players are excluded from being the Mutant because the puzzle states the Mutant reveals their true role after death.
- The public facts force Aoife as the Vortox and Tom as the Minion. The exact minion character is not forced by this model, so the puzzle output reports the forced minion holder rather than an exact minion role.

## Puzzle 12a: Thunderstruck

- Added metadata classes for `Lunatic`, `Courtier`, and `Mayor`.
- Modeled Doomsayer deaths puzzle-locally. The Spy can register as good to Doomsayer, so a good caller can kill the Spy even though the Spy is evil.
- Modeled the Courtier branch explicitly: if Sarah were the Courtier who drunked the Vortox, Townsfolk information would be correct; otherwise Vortox false information applies.
- Modeled Spy registration to Empath as a local predicate. This keeps the base registration helpers stable while preserving the puzzle's special rule that Spy misregistration is already false information and is not inverted by Vortox.

## Puzzle 12b: Thunderstruck

- Reused the puzzle-local Doomsayer, Courtier, and Spy-registration logic from 12a, extended to Librarian and Investigator checks.
- For Librarian information, treated a Spy in the checked pair as a possible false "Lunatic" registration. If the Vortox is active, a reported yes can therefore come either from Vortox false information or from Spy misregistration.

## Puzzle 13: Clockblocking

- Reused the Trouble Brewing outsider-count pattern: zero Outsiders by default, two if Baron is in play.
- Split Poisoner timing into night-one information and night-two/day-two effects after Aoife's execution. If Aoife is the Poisoner, the second context is inactive.
- Modeled Clockmaker distance as an exact distance predicate local to the puzzle, because the existing `Clockmaker` helper only covers "Demon next to Minion".

## Puzzle 14: New Super Marionette Bros

- Reused the Marionette adjacency rule from puzzle 6 but did not treat a Marionette's shown information as factual.
- Included `Drunk` with count zero so existing Townsfolk claim helpers can still express "shown a Townsfolk token" without allowing any Outsiders in the final worlds.
- Split Poisoner poisoning into two contexts so Rob can be poisoned for both Empath readings while other night-one and night-two information remains separately constrained.

## Puzzle 15: Wake Up and Choose Violets

- Added `EvilTwin.pairIsOneOf` to model the Evil Twin's opposing good twin as setup state. This matters separately from a role's information: the actual Evil Twin must be paired with a good player, so a public twin-pair claim cannot resolve to two evil players.
- Kept No Dashii poisoning puzzle-local. The No Dashii only explains why adjacent Townsfolk information can be arbitrary; it does not make an evil player's public statement truthful.
- Allowed up to two Snake Charmer tokens in this puzzle only, because the published twin claims require a possible good Snake Charmer and an Evil Twin appearing as the same claimed role.

## Puzzle 16: Who Watches the Watchmen?

- Added `Nightwatchman` as a Townsfolk role class with metadata only. The selected-player information is encoded locally because this puzzle uses Tim's denial of receiving Nightwatchman information rather than a normal Nightwatchman info claim.
- Modeled Olivia's Empath readings with explicit alive-neighbor sets. Her night-one read checks You and Jasmine, but after You dies on night two her alive neighbors are Tim and Jasmine.
- Added local death-timeline constraints for the Imp and Scarlet Woman. A night death after an executed Imp is possible only if a living Scarlet Woman can have replaced them.

## Puzzle 17: The Missing Piece

- Added `Puzzlemaster` as an Outsider role class and modeled its drunk player as a separate poison/drunk context. This is intentionally distinct from the `Drunk` character: the Puzzlemaster target keeps their actual role but their information can be arbitrary.
- Used explicit Demon-at-night predicates for Fortune Teller and Slayer timing because the Scarlet Woman can create a current Demon that differs from the starting Imp after executions or an Imp self-kill.
- Kept the Fortune Teller red herring local to the puzzle. The legal worlds do not force a unique evil team, but they do force Steph as the Puzzlemaster-drunk player, which is the puzzle's requested answer.

## Puzzle 18: X and the City

- Added `Xaan` as a Minion role class with metadata only.
- Modeled `X` as a SAT branch rather than a post-processing guess. Each branch enforces exactly `X` Outsiders and suppresses Townsfolk information only on night `X`, matching the Xaan's poisoning window.
- Kept the Snake Charmer choices local and night-scoped. A sober Snake Charmer choosing the Demon would change roles, so each unpoisoned choice constrains that night's chosen player not to be the Leviathan.

## Puzzle 19: He Could Be You, He Could Be Me

- Modeled Jasmine's public Slayer shot as a working sober Slayer ability. Oscar must therefore either be the Imp or a sober Recluse registering as the Imp; if Oscar were the Imp, a living Scarlet Woman would be required for the game to continue.
- Used alive-neighbor Empath readings again because You is executed before Aoife's second read, changing Aoife's relevant neighbors from You/Sula to Fraser/Sula.
- Replaced the generic night-two Poisoner effect with a timed local constraint. Since Undertaker wakes after the Imp, a Poisoner who died that night, or who became the Imp because Matt self-killed, no longer poisons Olivia's Undertaker information.

## Puzzle 20: The Three Wise Men

- Added `Virgin` as a Townsfolk role class with metadata only. The day-one nomination result is modeled locally: if Mary is a sober Virgin, Balthazar's nomination doing nothing means Balthazar was not a Townsfolk.
- Reused the duplicate `VillageIdiot` pattern with a generalized local drunk-extra constraint: when multiple actual Village Idiots are in play, exactly one of those Village Idiots is drunk separately from the `Drunk` Outsider character.
- Kept the Baron outsider-count rule local. With Mary as Baron, Joseph can be the Saint and Gabriel can be the Drunk, which also explains Gabriel's Ravenkeeper claim.

## Puzzle 21: Eight Jugglers Juggling

- Reused the duplicate-role setup pattern for the Bootlegger rule "Every Townsfolk is a Juggler": role uniqueness is disabled for this puzzle, while Leviathan, Goblin, and Drunk are each fixed to exactly one.
- Modeled each Juggler statement as an exact count only when the speaker is an actual Juggler. Evil players and the Drunk keep arbitrary information.

## Puzzle 22: One in the Chamber

- Added `Chambermaid` as a Townsfolk role class with metadata only. Its wake-count semantics are puzzle-local because they depend on explicit night timing, deaths, and starpass handling.
- Used the puzzle author's Chambermaid timing assumptions from the source thread: minions learning they became the Imp after a normal Imp self-kill do not count as waking due to their own ability, but a Scarlet Woman catching an Imp death does count.
- Modeled the Drunk as waking like the character they think they are for Chambermaid purposes.
- Reused the timed Poisoner rule: a Poisoner who is dead or has become the Imp before later information/action resolution no longer poisons those later effects.

## Puzzle 23: Goblincore

- Modeled `Lunatic` as an actual Outsider who can claim another role and provide arbitrary information. This differs from `Drunk`: the Lunatic is not constrained by the claimed role's information at all.
- Added a local current-Demon check for Sula's Slayer shot. If Aoife had self-killed as the Imp, the Goblin would be the current Demon on day two, so a sober Slayer shot on that player would not be "nothing happened."

## Puzzle 24: The Ultimate Blunder

- Modeled Steph's Fortune Teller checks against the current Demon at each night. This allows the night-two yes to come from an Imp self-kill/starpass path, not only from the starting Imp.
- Split Steph's two Fortune Teller checks into separate poison contexts so a night-two poison does not erase the night-one check.
- Modeled Olivia's Klutz choice locally: if Olivia is a sober/healthy Klutz, choosing Adam and the game not ending means Adam is good. In the final world Olivia is poisoned, so that choice does not constrain Adam.

## Puzzle 25: Clockdoku

- Implemented Clockdoku as a standalone row/column exact-cover solver rather than forcing it through the player-role SAT model. There are no players, claims, or night timing, only grid constraints.
- The row/column validator encodes the puzzle's Baron/Poisoner branch directly: Baron lines must include Saint and Recluse, while Poisoner lines include no Outsiders.

## Puzzle 26: A Major Problem

- Added `Soldier` as a Townsfolk role class with metadata only. Josh dying at night is modeled locally: an actual Soldier must be poisoned on that night, otherwise the death is impossible.
- Modeled Dan's Slayer shot against the current Demon after Josh's night-two death, so an Imp self-kill/starpass branch cannot hide behind the starting role assignment.
- The model leaves multiple worlds for the irrelevant night-three poison target, but Tom as Imp and Matthew as Poisoner are forced.

## Puzzle 27: Is This a Legion Game?

- Added `Legionary` as a Townsfolk role class with metadata only. Its count is modeled locally because it depends on clockwise seating, living players, and the next living Legionary each night.
- Disabled global role uniqueness for this puzzle and re-applied uniqueness to every role except `Legionary`, matching the homebrew setup rule that can add multiple Legionaries.
- Used explicit alive sets for Legionary and Empath information. Tom is executed before the second night's information, while You dies later that night and is still alive for the night-two Legionary counts.

## Puzzle 28: A Study in Scarlet

- Added `Oracle` as a Townsfolk role class with metadata only. The dead-player count is encoded locally because this puzzle's timing only needs Sarah's night-two view of Adam and You as dead.
- Made No Dashii poisoning and Fortune Teller Demon checks night-aware in the puzzle file. If the Scarlet Woman catches an executed Demon, later No Dashii poisoning and Demon registration come from the replacement Demon, not the starting seat.
- Treated Scarlet Woman as not waking on night one unless her ability triggers. This matters for You's Chambermaid check on Adam and Sarah.

## Puzzle 29: A Dreamer? I'm Not the Only One

- Reused the duplicate-role setup pattern for the Bootlegger rule "Every Townsfolk is a Dreamer."
- Split Dreamer information into night-one and night-two poison contexts. Steph's otherwise contradictory first Dreamer statement is explained by Jasmine being the Poisoner and poisoning Steph on night one.

## Puzzle 30: The Babel Fish Is a Dead Giveaway

- Added `Atheist` as a Townsfolk role class with metadata only. The actual Atheist game is handled as a paired-puzzle branch where all information is arbitrary, while the non-Atheist branch is a normal six-player SAT model.
- Kept paired-game orchestration puzzle-local. Each side is tested as the non-Atheist game; a satisfying non-Atheist world on the right means the left game is the genuine Atheist game.
- Modeled the Artist's "is the Drunk" question with role registration rather than actual role identity. This matters because Louisa is the Spy in the non-Atheist game and can register as the Drunk to Shan.

## Puzzle 31: No, Your Other Left

- Modeled Chef adjacent-evil pairs with per-pair registration variables. This preserves the intended interaction where Fraser as Recluse can register as evil for exactly one of the two adjacent pairs that include him.
- Reused timed Poisoner contexts and made night-three Poisoner poisoning inactive if the Poisoner died on night two or was executed on day two.
- Added local night-death constraints for Imp deaths. A night-dead Imp only remains compatible with a later night death if a living Scarlet Woman could catch the starpass.

## Puzzle 32: Prepare for Juggle, and Make It Double

- Modeled Juggler results on night two, not night one. The public juggle happens on day one, but the Juggler learns the result that night, so Dan can be poisoned on night two to receive an arbitrary zero.
- Used the displayed final Empath pair as a timing constraint: Sula's final reading is after Fraser's night-three death, so a Fraser Poisoner cannot be the source of night-three misinformation.
- Kept Baron outsider-count manipulation local. In the final world no Baron is in play, so the single Outsider is Fraser as Saint and there is no actual Drunk.

## Puzzle 33: Twice Is Coincidence, Thrice Is Proof

- Made Fortune Teller checks use the current Demon after night deaths. This matters for Imp self-kill branches: the Minion can become the Demon before Oscar's later checks resolve.
- Extended the Poisoner timing model for starpasses. If Olivia starts as Imp and self-kills on night two, the starting Poisoner is now the Imp and cannot keep poisoning on night three.
- Added a local guard against a one-minion self-kill chain. If Olivia self-kills into Jasmine and Jasmine is the listed night-three death, there is no remaining Minion to explain the game continuing through Jasmine's Ravenkeeper information.

## Puzzle 34: The Vortox Conjecture

- Added `Witch` and `Mathematician` role classes with metadata only. The Witch curse target, No Dashii poisoning, Vortox false information, and Mathematician malfunction counts are puzzle-local because they depend on the exact public timeline and which players acted in each period.
- Modeled good players as truthful about their shown role by allowing each non-You player to be either their claimed Townsfolk role or one of the hidden evil roles. You is fixed as the Mathematician because the puzzle states You are not evil.
- Modeled No Dashii poisoning as the closest Townsfolk in each direction, skipping evil players. This matters in candidate worlds where the Demon is adjacent to the Witch rather than to a Townsfolk.
- Counted Mathematician malfunctions separately from the shown Mathematician number. The Mathematician does not count their own false Vortox number, but their shown number must still be false in a Vortox game.

## Puzzle 35: Typhon Season

- Reused `LordOfTyphon` metadata and modeled its setup locally: when it is in play, both `Poisoner` and `Spy` are in play and the Lord of Typhon must sit between its two Minions.
- Kept the Imp branch separate from the Lord of Typhon branch. Imp worlds have exactly one Minion and the default single Outsider; Lord of Typhon worlds have the extra Minion and no fixed Outsider count.
- Used role registration for the Librarian, Fortune Teller, Investigator, and Empath claims so the Spy can register as the Drunk, a good role, or evil as needed by each information source.

## Puzzle 36: What Is Your Weapon of Choice?

- Added `BOTCModel.addDrunkThinksOutOfPlayRole` and applied it to this puzzle's Drunk candidates. The earlier claim helper only allowed a Drunk to think they were a Townsfolk; this puzzle also needs the standard setup detail that the Drunk's shown Townsfolk token is out of play.
- Modeled Slayer shots against the current Demon rather than only the starting Imp. This matters because an Imp self-kill or Scarlet Woman catch can change who would die to a later Slayer shot.
- Added puzzle-local current-Demon predicates for day two, night three, and day three. They cover Josh self-killing on night two, Oscar being executed on day two, and a Scarlet Woman replacing an executed Imp.
- Split Fortune Teller and Poisoner timing by night. Olivia's two checks can be affected independently, while the final Slayer shot can only be arbitrary if Adam is poisoned for the day-three context.

## Puzzle 37: New Super Marionette Bros U

- Reused the out-of-play Drunk-token helper from puzzle 36. This is necessary to distinguish You being a poisoned Undertaker from You being the Drunk while another actual Undertaker token is in play.
- Modeled Marionette as a Minion neighboring the starting Imp, but did not make Marionette-shown Undertaker information factual. The Storyteller can show arbitrary information to a Marionette.
- Made Poisoner timing stop if the Poisoner dies that night or becomes the Imp. The Reddit answer thread calls out that reminder tokens disappear when the Poisoner dies or changes character, so night-three misinformation requires a still-living Poisoner.

## Puzzle 38: Snakes on a Plane

- Reused current-Demon predicates for Snake Charmer picks and Fortune Teller checks. A Snake Charmer who is sober and healthy constrains the chosen player not to be the current Demon at that night's context.
- Modeled Dan's night-two death as a possible Imp self-kill/starpass. In the final world Dan starts as the Imp and Tim, the Baron, becomes the current Demon after night two.
- Kept the displayed Empath pairs explicit rather than deriving them from live neighbors, because the puzzle image states the exact pairs attached to each read.

## Puzzle 39: Squid Game

- Modeled No Dashii poisoning again as the nearest Townsfolk in each direction, skipping evil players and Outsiders. This is required for Jasmine as No Dashii to poison Aoife and You while Matt is the neighboring Mutant.
- Counted Mathematician abnormalities as false information caused by another ability. A poisoned player who happens to receive true information does not increase the Mathematician count.
- Treated a living Mutant as able to claim a Townsfolk role with arbitrary information, while excluding dead players from being the Mutant because the puzzle states the Mutant reveals their role after death.

## Puzzle 40: Nine Lives

- Added `Butler` as an Outsider role class with metadata only.
- Used registration-aware information for Investigator and Fortune Teller claims. In the final world Steph is the Recluse and can register as the Scarlet Woman to You.
- Modeled the larger Trouble Brewing outsider setup locally: the default outsider count is two, and a Baron makes all four listed Outsiders present.
