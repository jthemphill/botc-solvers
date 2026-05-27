import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

export default defineConfig({
  root: "src",
  publicDir: "../public",
  base: process.env.BASE_PATH || "/",
  build: {
    outDir: "../browser-dist",
    emptyOutDir: true,
  },
  plugins: [react()],
  worker: {
    format: "es",
  },
});
