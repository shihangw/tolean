/** Line icons on a 16-unit grid, drawn with the text colour. */
const paths = {
  check: <path d="m3.5 8.5 3 3 6-7" />,
  x: <path d="m4.5 4.5 7 7m0-7-7 7" />,
  alert: (
    <>
      <path d="M8 2.2 14.3 13.3H1.7z" />
      <path d="M8 6.6v3m0 1.9v.1" />
    </>
  ),
  info: (
    <>
      <circle cx="8" cy="8" r="6" />
      <path d="M8 7.3v3.9m0-6v.1" />
    </>
  ),
  circle: <circle cx="8" cy="8" r="5.5" strokeDasharray="2.2 2.2" />,
  lock: (
    <>
      <rect x="3.5" y="7" width="9" height="6.5" rx="1.6" />
      <path d="M5.5 7V5.2a2.5 2.5 0 0 1 5 0V7" />
    </>
  ),
  plus: <path d="M8 3.5v9M3.5 8h9" />,
  share: (
    <>
      <path d="M6.6 9.4 9.4 6.6" />
      <path d="m8.7 4.2 1.2-1.2a2.6 2.6 0 0 1 3.7 3.7l-1.2 1.2M7.3 11.8 6.1 13a2.6 2.6 0 0 1-3.7-3.7l1.2-1.2" />
    </>
  ),
  sun: (
    <>
      <circle cx="8" cy="8" r="2.8" />
      <path d="M8 1.6v1.5m0 9.8v1.5M1.6 8h1.5m9.8 0h1.5M3.5 3.5l1 1m7 7 1 1m-9 0 1-1m7-7 1-1" />
    </>
  ),
  moon: <path d="M13.1 9.7A5.5 5.5 0 0 1 6.3 2.9a5.5 5.5 0 1 0 6.8 6.8z" />,
  github: (
    <path
      fill="currentColor"
      stroke="none"
      d="M8 1.6a6.4 6.4 0 0 0-2 12.5c.3 0 .4-.1.4-.3v-1.2c-1.8.4-2.2-.8-2.2-.8-.3-.7-.7-.9-.7-.9-.6-.4 0-.4 0-.4.6 0 1 .7 1 .7.6 1 1.5.7 1.9.5 0-.4.2-.7.4-.9-1.4-.2-2.9-.7-2.9-3.2 0-.7.3-1.3.7-1.7-.1-.2-.3-.8.1-1.7 0 0 .5-.2 1.8.7a6 6 0 0 1 3.2 0c1.2-.8 1.8-.7 1.8-.7.3.9.1 1.5.1 1.7.4.4.7 1 .7 1.7 0 2.5-1.5 3-2.9 3.2.2.2.4.6.4 1.2v1.8c0 .2.1.4.4.3A6.4 6.4 0 0 0 8 1.6z"
    />
  ),
  book: (
    <>
      <path d="M2.5 3.4c2-.7 3.8-.5 5.5.9 1.7-1.4 3.5-1.6 5.5-.9v9.1c-2-.7-3.8-.5-5.5.9-1.7-1.4-3.5-1.6-5.5-.9z" />
      <path d="M8 4.3v9.1" />
    </>
  ),
  play: <path d="M5 3.4v9.2l7.2-4.6z" fill="currentColor" />,
  arrow: <path d="M3.5 8h9m-3.5-3.5L12.5 8 9 11.5" />,
  chevron: <path d="m4.5 6.5 3.5 3.5 3.5-3.5" />,
  folder: <path d="M2.2 4.6c0-.7.5-1.2 1.2-1.2h2.8l1.4 1.5h5c.7 0 1.2.5 1.2 1.2v5.8c0 .7-.5 1.2-1.2 1.2H3.4c-.7 0-1.2-.5-1.2-1.2z" />,
  layers: (
    <>
      <path d="m8 2.2 5.8 3.1L8 8.4 2.2 5.3z" />
      <path d="m2.2 8.2 5.8 3.1 5.8-3.1m-11.6 2.9L8 14.2l5.8-3.1" />
    </>
  ),
  turnstile: <path d="M4 3v10M4 8h8" />,
} as const;

export type IconName = keyof typeof paths;

export function Icon({ name, size = 16, className }: { name: IconName; size?: number; className?: string }) {
  return (
    <svg
      className={className == null ? 'icon' : `icon ${className}`}
      viewBox="0 0 16 16"
      width={size}
      height={size}
      fill="none"
      stroke="currentColor"
      strokeWidth="1.5"
      strokeLinecap="round"
      strokeLinejoin="round"
      aria-hidden="true"
    >
      {paths[name]}
    </svg>
  );
}

/** Tolean's mark: the turnstile ⊢ that Lean prints before a goal, in a rounded square. */
export function Mark({ size = 26 }: { size?: number }) {
  return (
    <svg className="mark" viewBox="0 0 32 32" width={size} height={size} aria-hidden="true">
      <rect x="1.5" y="1.5" width="29" height="29" rx="8" fill="var(--accent)" />
      <path d="M11 8.5v15M11 16h11" fill="none" stroke="var(--on-accent)" strokeWidth="3" strokeLinecap="round" />
      <circle cx="22.5" cy="23" r="2" fill="var(--on-accent)" opacity=".7" />
    </svg>
  );
}
