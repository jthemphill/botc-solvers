import { KissatBackend } from "../model/sat";

let loaded: Promise<KissatBackend> | undefined;

export function loadKissat(): Promise<KissatBackend> {
  if (loaded === undefined) {
    loaded = KissatBackend.create();
  }
  return loaded;
}
