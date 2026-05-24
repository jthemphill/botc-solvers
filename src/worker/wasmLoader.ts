import wasmUrl from "../../vendor/kissat-js/kissat-emscripten.wasm?url";
import { KissatBackend } from "../model/sat";

let loaded: Promise<KissatBackend> | undefined;

export function loadKissat(): Promise<KissatBackend> {
  if (loaded === undefined) {
    (globalThis as unknown as { Module?: unknown }).Module = {
      locateFile: (path: string) => (path.endsWith(".wasm") ? wasmUrl : path),
    };
    loaded = KissatBackend.create();
  }
  return loaded;
}
