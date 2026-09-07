import { BOTCModel } from "../src/model/model";
import { roleByName } from "../src/model/roleRegistry";
import { KissatBackend } from "../src/model/sat";

const backend = await KissatBackend.create();
const results = [];
for (const size of [10, 20, 40, 80]) {
  const game = new BOTCModel(["A"], { characters: [roleByName("Chef")], backend });
  const start = performance.now();
  const values = Array.from({ length: size }, (_, i) => game.newBool(`choice_${i}`));
  game.addExactlyN(values, Math.floor(size / 2));
  const buildMs = performance.now() - start;
  const result = await game.solve();
  results.push({ case: `choose_${size / 2}_of_${size}`, buildMs, ...result.metrics });
}
for (const size of [4, 8]) {
  const game = new BOTCModel(
    Array.from({ length: size }, (_, i) => `P${i}`),
    { characters: ["Chef", "Artist"].map(roleByName), uniqueCharacters: false, backend },
  );
  const result = await game.solve();
  results.push({ case: `enumerate_${size}_binary_roles`, worlds: result.worlds.length, ...result.metrics });
}
console.log(
  JSON.stringify(
    { backend: "bundled Kissat (rebuilds per solve; no incremental API exported by this adapter)", results },
    null,
    2,
  ),
);
