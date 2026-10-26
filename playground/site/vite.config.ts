import react from '@vitejs/plugin-react';
import { defineConfig } from 'vite';

// GitHub Pages serves the site under /tolean/, so every asset path is relative.
export default defineConfig({ base: './', plugins: [react()] });
