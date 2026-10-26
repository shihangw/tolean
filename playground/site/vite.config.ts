import react from '@vitejs/plugin-react';
import { defineConfig } from 'vite';

// GitHub Pages serves the site under /tolean/, so every asset path is relative.
// The build id busts the browser's cache of lean-worker.js, which Vite does not hash.
export default defineConfig({
  base: './',
  plugins: [react()],
  define: { __BUILD_ID__: JSON.stringify(Date.now().toString(36)) },
});
