open util/graph[Player] as seats

// Says that something will stay unchanged between timesteps
let same[r] { ((r) = (r)') }

/**
 * The Day/Night cycle.
 */

enum Time { Day, Night }

enum Number { One, Two }

one sig CurrentTime {
    var time: Time,
    var which: Number,
    var waking: lone Role
}

fact begin_on_night_one {
    CurrentTime.time = Night
    CurrentTime.which = One
}

/**
 * The cast of characters, in wake order.
 */

enum Role {
    Poisoner,
    Monk,
    ScarletWoman,
    Imp,
    Ravenkeeper,
    Washerwoman,
    Librarian,
    Investigator,
    Chef,
    Empath,
    FortuneTeller,
    Undertaker,
    Butler,
    Spy,
    Drunk,
    Baron,
    Recluse,
    Slayer
}

fun townsfolk: set Role {
     Monk + Ravenkeeper + Washerwoman + Librarian + Investigator + Chef + Empath + FortuneTeller + Undertaker + Slayer
}

fun outsiders: set Role {
    Drunk + Recluse
}

fun minions : set Role {
    Poisoner + ScarletWoman + Spy + Baron
}

fun demons: set Role {
    Imp + Recluse
}

pred registers_as_townsfolk[player: Player] {
    player.role in townsfolk + Spy
}

pred registers_as_outsider[player: Player] {
    player.role in outsiders + Spy
}

pred registers_as_good[player: Player] {
    registers_as_townsfolk[player] or registers_as_outsider[player]
}

pred registers_as_minion[player: Player] {
    player.role in minions + Recluse
}

pred registers_as_demon[player: Player] {
    player.role in demons + Recluse
}

pred registers_as_evil[player: Player] {
    registers_as_minion[player] or registers_as_demon[player]
}

/**
 * Player state
 */

enum Shroud { Dead }

sig Player {
    person: one Person,
    left: one Player,
    right: one Player,
    var role: one Role,
    var shroud: lone Shroud,
}

fact seven_players {
    // 1 Demon
    one p: Player { p.role in demons }

    // 1 Minion
    one p: Player { p.role in minions }

    // 0 Outsiders by default
    no get_role[Baron] => {
        no p: Player | p.role in outsiders
    }

    // 2 Outsiders if Baron is in play
    some get_role[Baron] => {
        some disj p2, p3: Player {
            all p: Player {
                p in p2 + p3 <=> p.role in outsiders
            }
        }
    }
}

enum Person { You, Matthew, Dan, Tom, Sula, Fraser, Josh }

fact no_duplicate_people {
    all disj p1, p2: Player | p1.person != p2.person
}

fact players_sit_in_a_circle {
    always {
        seats/ring[left]
        seats/ring[right]
        all p: Player | p.left.right = p
        all p: Player | p.right.left = p
        all p: Player | p.left != p
        all p: Player | p.right != p
    }
}

fact people_are_written_in_clockwise_order {
    all p: Player | p.left.person = next[p.person]
}

/**
 * Mechanics of specific roles
 */

// Fortune Teller

one sig RedHerring {
    player: one Player
}

pred fortune_teller_yes(fortune_teller: Player, checked_players: set Player) {
    CurrentTime.waking = FortuneTeller
    ability_works[fortune_teller, FortuneTeller]

    some pinged_player: checked_players {
        registers_as_demon[pinged_player] or pinged_player = RedHerring.player
    }
}

pred fortune_teller_no(fortune_teller: Player, checked_players: set Player) {
    CurrentTime.waking = FortuneTeller
    ability_works[fortune_teller, FortuneTeller]

    no pinged_player: checked_players {
        registers_as_demon[pinged_player] or pinged_player = RedHerring.player
    }
}

// Poisoner

one sig PoisonedPlayer {
    var player: lone Player
}

// Only two events can move the Poisoner token: the Poisoner's ability, or sunset (which clears the poison)
fact poisoned_player_frame_conditions {
    always {
        same[PoisonedPlayer.player] or
        lone p: Player | sunset[p] or
        some p1, p2: Player | poisons_player[p1, p2]
    }
}

fact nobody_starts_poisoned {
    PoisonedPlayer.player = none
}

pred poisons_player[poisoner: one Player, poisoned: one Player] {
    CurrentTime.waking = Poisoner
    ability_works[poisoner, Poisoner]

    PoisonedPlayer.player' = poisoned

    // Nothing else changes during this timestep
    same[Player.role]
    same[Player.shroud]
    same[CurrentTime.time]
    same[CurrentTime.which]
    same[CurrentTime.waking]
}

// Chef

pred claims_chef_zero[chef: Player] {
    (CurrentTime.waking = Chef and ability_works[chef, Chef]) => {
        no disj p1, p2: Player {
            p1.left = p2
            registers_as_evil[p1]
            registers_as_evil[p2]
        }
    }
}

// Washerwoman

pred claims_washerwoman_sees_as[washerwoman: one Player, seen_people: set Person, seen_role: Role] {
    (CurrentTime.waking = Washerwoman and ability_works[washerwoman, Washerwoman]) => {
        some p: seen_people | saw_as[p, seen_role]
    }
}

// Ravenkeeper

pred claims_ravenkeeper_sees_as[ravenkeeper: one Player, seen_person: Person, seen_role: Role] {
    (CurrentTime.waking = Ravenkeeper and ability_works[ravenkeeper, Ravenkeeper]) => {
        saw_as[seen_person, seen_role]
    }
}

// Scarlet Woman

fact scarlet_woman_swaps {
    always {
        // If there is a Scarlet Woman in the game with a working ability
        some scarlet_woman: get_role[ScarletWoman] | ability_works[scarlet_woman, ScarletWoman] => {
            // And if the Imp is about to die
            some imp: Player | imp.role = Imp and no imp.shroud and imp.shroud' = Dead => {
                // And there are still five living players (counting the Imp who is about to die)
                (some disj p1, p2, p3, p4, p5: Player {
                    all p: p1 + p2 + p3 + p4 + p5 | p.shroud = none
                }) => {
                    // Then the Scarlet Woman will become a new Imp
                    scarlet_woman.role' = Imp
                }
            }
        }
    }
}

// Imp

pred imp_kills[killer: Player, killed: Player] {
    ability_works[killer, Imp]
    CurrentTime.waking = Imp

    killed.shroud' = Dead
    all unkilled_player: Player - killed {
        unkilled_player.shroud' = unkilled_player.shroud
    }

    // If the Imp kills themself and at least one Minion is alive, a Minion becomes an Imp.
    killer = killed => {
        some minion: get_role[minions] | minion.shroud = none => {
            minion.role' = Imp
            all other_player: Player | other_player.role' = other_player.role
        }
    }

    // If the Imp doesn't starpass, nobody changes role
    killed.role != Imp => same[Player.role]

    same[CurrentTime.time]
    same[CurrentTime.which]
    same[CurrentTime.waking]
}

// Undertaker
pred claims_undertaker_saw_as[undertaker: one Player, seen_person: Person, seen_role: Role] {
    (CurrentTime.waking = Undertaker and ability_works[undertaker, Undertaker]) => {
        saw_as[seen_person, seen_role]
    }
}

/**
 * The flow of time, and events that change the state of the Grimoire
 */

enum Event { Sunrise, Sunset, Wake, ImpKilling, DecisionTime }

pred sunrise {
    // Night 1 to Day 1
    CurrentTime.time = Night
    CurrentTime.time' = Day
    CurrentTime.which' = CurrentTime.which
    CurrentTime.waking' = none

    PoisonedPlayer.player' = PoisonedPlayer.player
    Player.role' = Player.role
    Player.shroud' = Player.shroud
}

pred sunset[executed_player: lone Player] {
    // The player on the block is executed
    executed_player.shroud' = Dead

    // The poisoner's effect wears off at sunset
    PoisonedPlayer.player' = none

    // Day 1 to Night 2
    CurrentTime.time = Day
    CurrentTime.time' = Night
    CurrentTime.which' = next[CurrentTime.which]
    CurrentTime.waking' = none

    // Nobody dies except the executed player
    all p: Player - executed_player | same[p.shroud]

    // If the executed player isn't an Imp, nobody changes role
    executed_player.role != Imp => same[Player.role]
}

pred wake[woken_role: one Role] {
    // We must not be at this role's place in the night order yet
    no CurrentTime.waking or CurrentTime.waking in woken_role.prevs

    // Set the waking role to this one
    CurrentTime.waking' = woken_role

    same[Player.role]
    same[Player.shroud]
    same[CurrentTime.time]
    same[CurrentTime.which]
}

pred decision_time {
    some p: Player | p.shroud = none and p.role = Imp

    // End the simulation
    CurrentTime.time' = CurrentTime.time
    CurrentTime.which' = CurrentTime.which
    Player.role' = Player.role
    Player.shroud' = Player.shroud
    PoisonedPlayer.player' = PoisonedPlayer.player
}

fact possible_events {
    always {
        sunrise or
        (lone executed_player: Player | sunset[executed_player]) or
        (some role: Role | wake[role])
        (some disj poisoner, poisoned: Player {
            poisons_player[poisoner, poisoned]
        }) or
        (some imp, killed_player: Player {
            imp_kills[imp, killed_player]
        }) or decision_time
    }
}

/**
 * Mechanics that help with logical deduction
 */

pred is_liar(p: Player) {
    p.role in Drunk + minions + demons
}

pred ability_works(p: Player, ability_role: Role) {
    p.role = ability_role
    p.shroud = none or (p.role in Ravenkeeper + Spy + Recluse)
    p not in PoisonedPlayer.player
}

pred claims_role(claiming_person: Person, claimed_role: Role) {
    one player: get_person[claiming_person] {
        is_liar[player] or player.role = claimed_role
    }
}

fun get_role[r: set Role]: Player {
    { player: Player | player.role in r }
}

fun get_person[p: Person]: Player {
    { player: Player | player.person = p }
}

pred saw_as[seen_person: Person, seen_role: Role] {
    all seen_player: get_person[seen_person] {
        seen_role in townsfolk => registers_as_townsfolk[seen_player]
    }
}

fact living_demon_at_the_end {
    always {
        eventually {
            some p: Player | p.role in demons and no p.shroud
        }
    }
}

fact you_are_good {
    always {
        one you: get_person[You] | you.role in townsfolk + outsiders
    }
}

// fact josh_executed_day_one {
//     eventually {
//         CurrentTime.time = Day
//         CurrentTime.which = One
//         sunset[get_person[Josh]]
//     }
// }

// fact matthew_killed_night_two {
//     eventually {
//         CurrentTime.time = Night
//         CurrentTime.which = Two
//         get_person[Matthew].shroud = Dead
//     }
// }

fact claims_you {
    always {
        claims_role[You, Slayer]
    }

    eventually {
        CurrentTime.time = Day
        CurrentTime.which = Two
        ability_works[get_person[You], Slayer] => {
            get_person[Fraser].role not in demons
        }
    }
}

// fact claims_matthew {
//     always {
//         claims_role[Matthew, Ravenkeeper]
//     }

//     eventually {
//         CurrentTime.time = Night
//         CurrentTime.which = Two
//         claims_ravenkeeper_sees_as[get_person[Matthew], Josh, Imp]
//     }
// }

// fact claims_dan {
//     always {
//         claims_role[Dan, Undertaker]
//     }

//     eventually {
//         CurrentTime.which = Two
//         claims_undertaker_saw_as[get_person[Dan], Josh, Poisoner]
//     }
// }

// fact claims_tom {
//     always {
//         claims_role[Tom, FortuneTeller]

//         one tom: get_person[Tom] {
//             CurrentTime.which = One => {
//                 fortune_teller_no[tom, tom + get_person[Sula]]
//             }
//             CurrentTime.which = Two => {
//                 fortune_teller_yes[tom, tom + get_person[Josh]]
//             }
//         }
//     }
// }

// fact claims_sula {
//     always {
//         claims_role[Sula, Chef]
//     }

//     eventually {
//         CurrentTime.which = One
//         claims_chef_zero[get_person[Sula]]
//     }
// }

// fact claims_fraser {
//     always {
//         claims_role[Fraser, Recluse]
//     }
// }

// fact claims_josh {
//     always {
//         claims_role[Josh, Washerwoman]
//     }

//     eventually {
//         CurrentTime.which = One
//         claims_washerwoman_sees_as[get_person[Josh], Dan + Sula, Undertaker]
//     }
// }

run {} for exactly 7 Player, 10 steps