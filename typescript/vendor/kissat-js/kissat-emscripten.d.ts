declare const module: KissatEmscriptenModule;

export default module;

export interface KissatEmscriptenModule {
  calledRun?: boolean;
  ccall(ident: string, returnType: "number", argTypes: readonly string[], args: readonly (number | string)[]): number;
  ccall(ident: string, returnType: "string", argTypes: readonly string[], args: readonly (number | string)[]): string;
  ccall(ident: string, returnType: null, argTypes: readonly string[], args: readonly (number | string)[]): null;
}
