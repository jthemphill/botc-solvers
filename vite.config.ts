import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  root: "src",
  publicDir: "../public",
  build: {
    outDir: "../browser-dist",
    emptyOutDir: true,
  },
  plugins: [react()],
  worker: {
    format: "es",
  },
});
