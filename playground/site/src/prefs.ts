/**
 * Choices that one viewer makes for this browser: the colour theme and the
 * width of the claims panel. Storage can be blocked, so each choice then
 * lasts only for the visit.
 */
import { useCallback, useEffect, useState } from 'react';

function read(key: string): string | null {
  try {
    return localStorage.getItem(key);
  } catch {
    return null;
  }
}

function write(key: string, value: string): void {
  try {
    localStorage.setItem(key, value);
  } catch {
    // The choice lasts only for this visit.
  }
}

export type Theme = 'light' | 'dark';

const themeKey = 'tolean-playground-theme';
const darkQuery = '(prefers-color-scheme: dark)';

/**
 * The theme on the page. It follows the system until the viewer picks one.
 * index.html applies a stored pick before the page draws, so it does not flash.
 */
export function useTheme(): [Theme, () => void] {
  const [picked, setPicked] = useState<Theme | null>(() => {
    const t = read(themeKey);
    return t === 'light' || t === 'dark' ? t : null;
  });
  const [systemDark, setSystemDark] = useState(() => matchMedia(darkQuery).matches);
  useEffect(() => {
    const query = matchMedia(darkQuery);
    const follow = () => setSystemDark(query.matches);
    query.addEventListener('change', follow);
    return () => query.removeEventListener('change', follow);
  }, []);
  const theme = picked ?? (systemDark ? 'dark' : 'light');
  useEffect(() => {
    if (picked == null) delete document.documentElement.dataset.theme;
    else document.documentElement.dataset.theme = picked;
  }, [picked]);
  const toggle = useCallback(() => {
    const next = theme === 'dark' ? 'light' : 'dark';
    write(themeKey, next);
    setPicked(next);
  }, [theme]);
  return [theme, toggle];
}

const widthKey = 'tolean-playground-side-width';
export const sideWidths = { min: 300, max: 720, initial: 400 } as const;

const clamp = (n: number) => Math.round(Math.min(sideWidths.max, Math.max(sideWidths.min, n)));

/** The width of the claims panel, in pixels, and a way to set it. */
export function useSideWidth(): [number, (width: number) => void] {
  const [width, setWidth] = useState(() => {
    const stored = Number(read(widthKey));
    return stored > 0 ? clamp(stored) : sideWidths.initial;
  });
  const set = useCallback((next: number) => {
    const w = clamp(next);
    write(widthKey, String(w));
    setWidth(w);
  }, []);
  return [width, set];
}
