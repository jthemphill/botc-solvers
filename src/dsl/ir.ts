import type { ConstraintOrigin } from "../model/sat";
import { BoolVar, type BoolLike, type BOTCModel } from "../model/model";
import { Chef } from "../model/characters";
import type { Span } from "./tokens";

// The compiler does type checks on these operations before it makes SAT variables.
// Each reference is a signed index into this program. The first index is 1.
type Query =
  | "characterAt"
  | "hasCharacterTypeAt"
  | "isGood"
  | "isEvil"
  | "isGoodAt"
  | "isEvilAt"
  | "registersAsRole"
  | "fortuneTellerRedHerring"
  | "lleechHost"
  | "globalDrunk"
  | "poisoned"
  | "malfunctionCountAt";
type QueryNode = { [K in Query]: { readonly op: K; readonly args: Parameters<BOTCModel[K]> } }[Query];
export type BoolNode =
  | QueryNode
  | { readonly op: "constant"; readonly value: boolean }
  | { readonly op: "and" | "or"; readonly inputs: readonly number[] }
  | { readonly op: "exactly"; readonly inputs: readonly number[]; readonly count: number }
  | { readonly op: "chef"; readonly count: number; readonly name: string };
export interface TypedProgram {
  readonly origin?: ConstraintOrigin;
  readonly nodes: readonly { readonly expression: BoolNode; readonly span: Span }[];
  readonly root: number;
  readonly source: string;
  readonly name: string;
}
const ref = (value: BoolLike): number => (typeof value === "number" ? value : value.lit);

export class SemanticBuilder implements Pick<
  BOTCModel,
  Query | "neighbors" | "constantBool" | "allOf" | "anyOf" | "not" | "boolSumEquals"
> {
  readonly nodes: Array<{ expression: BoolNode; span: Span }> = [];
  span: Span = { start: 0, end: 0 };
  constructor(private readonly players: readonly string[]) {}
  private emit(expression: BoolNode): BoolVar {
    this.nodes.push({ expression, span: this.span });
    return new BoolVar(this.nodes.length, "semantic_reference");
  }
  withSpan<T>(span: Span, operation: () => T): T {
    const previous = this.span;
    this.span = span;
    try {
      return operation();
    } finally {
      this.span = previous;
    }
  }
  constantBool(value: boolean, _name: string): BoolVar {
    return this.emit({ op: "constant", value });
  }
  allOf(values: readonly BoolLike[], _name: string): BoolVar {
    return this.emit({ op: "and", inputs: values.map(ref) });
  }
  anyOf(values: readonly BoolLike[], _name: string): BoolVar {
    return this.emit({ op: "or", inputs: values.map(ref) });
  }
  not(value: BoolLike, _name: string): BoolVar {
    return new BoolVar(-ref(value), "semantic_negation");
  }
  boolSumEquals(values: readonly BoolLike[], count: number, _name: string): BoolVar {
    return this.emit({ op: "exactly", inputs: values.map(ref), count });
  }
  chefCount(count: number, name: string): BoolVar {
    return this.emit({ op: "chef", count, name });
  }
  neighbors(player: string): [string, string] {
    const index = this.players.indexOf(player);
    if (index < 0) throw new Error(`Unknown player: ${player}`);
    return [
      this.players[(index + 1) % this.players.length]!,
      this.players[(index + this.players.length - 1) % this.players.length]!,
    ];
  }
  characterAt(...args: Parameters<BOTCModel["characterAt"]>): BoolVar {
    return this.emit({ op: "characterAt", args });
  }
  hasCharacterTypeAt(...args: Parameters<BOTCModel["hasCharacterTypeAt"]>): BoolVar {
    return this.emit({ op: "hasCharacterTypeAt", args });
  }
  isGood(...args: Parameters<BOTCModel["isGood"]>): BoolVar {
    return this.emit({ op: "isGood", args });
  }
  isEvil(...args: Parameters<BOTCModel["isEvil"]>): BoolVar {
    return this.emit({ op: "isEvil", args });
  }
  isGoodAt(...args: Parameters<BOTCModel["isGoodAt"]>): BoolVar {
    return this.emit({ op: "isGoodAt", args });
  }
  isEvilAt(...args: Parameters<BOTCModel["isEvilAt"]>): BoolVar {
    return this.emit({ op: "isEvilAt", args });
  }
  registersAsRole(...args: Parameters<BOTCModel["registersAsRole"]>): BoolVar {
    return this.emit({ op: "registersAsRole", args });
  }
  fortuneTellerRedHerring(...args: Parameters<BOTCModel["fortuneTellerRedHerring"]>): BoolVar {
    return this.emit({ op: "fortuneTellerRedHerring", args });
  }
  lleechHost(...args: Parameters<BOTCModel["lleechHost"]>): BoolVar {
    return this.emit({ op: "lleechHost", args });
  }
  globalDrunk(...args: Parameters<BOTCModel["globalDrunk"]>): BoolVar {
    return this.emit({ op: "globalDrunk", args });
  }
  poisoned(...args: Parameters<BOTCModel["poisoned"]>): BoolVar {
    return this.emit({ op: "poisoned", args });
  }
  malfunctionCountAt(...args: Parameters<BOTCModel["malfunctionCountAt"]>): BoolVar {
    return this.emit({ op: "malfunctionCountAt", args });
  }
  finish(root: BoolLike, source: string, name: string, origin?: ConstraintOrigin): TypedProgram {
    return { nodes: this.nodes, root: ref(root), source, name, origin };
  }
}

/** After name resolution and type checks, make SAT constraints from the program. */
export function lower(program: TypedProgram, game: BOTCModel): BoolLike {
  const values: BoolLike[] = [];
  const resolve = (reference: number): BoolLike => {
    const value = values[Math.abs(reference) - 1];
    if (value === undefined) throw new Error("Invalid semantic reference.");
    return reference < 0 ? game.not(value, "semantic_not") : value;
  };
  for (const { expression: node, span } of program.nodes) {
    const value = game.withProvenance(
      { kind: "fact", id: program.name, ...program.origin, expression: program.source, span },
      () => {
        switch (node.op) {
          case "constant":
            return game.constantBool(node.value, program.name);
          case "and":
            return game.allOf(node.inputs.map(resolve), program.name);
          case "or":
            return game.anyOf(node.inputs.map(resolve), program.name);
          case "exactly":
            return game.boolSumEquals(node.inputs.map(resolve), node.count, program.name);
          case "chef":
            return Chef.learnsCount(game, node.count, node.name);
          case "characterAt":
            return game.characterAt(...node.args);
          case "hasCharacterTypeAt":
            return game.hasCharacterTypeAt(...node.args);
          case "isGood":
            return game.isGood(...node.args);
          case "isEvil":
            return game.isEvil(...node.args);
          case "isGoodAt":
            return game.isGoodAt(...node.args);
          case "isEvilAt":
            return game.isEvilAt(...node.args);
          case "registersAsRole":
            return game.registersAsRole(...node.args);
          case "fortuneTellerRedHerring":
            return game.fortuneTellerRedHerring(...node.args);
          case "lleechHost":
            return game.lleechHost(...node.args);
          case "globalDrunk":
            return game.globalDrunk(...node.args);
          case "poisoned":
            return game.poisoned(...node.args);
          case "malfunctionCountAt":
            return game.malfunctionCountAt(...node.args);
        }
      },
    );
    values.push(value);
  }
  return resolve(program.root);
}
