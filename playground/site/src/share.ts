import type { WorkspaceFile } from './lean.ts';

/** What a share link carries: the files a person wrote, and the workspace's name. */
export interface SharedWorkspace {
  readonly name: string;
  readonly files: readonly WorkspaceFile[];
}

const prefix = '#ws=';

async function pipe(
  bytes: Uint8Array<ArrayBuffer>,
  stream: CompressionStream | DecompressionStream,
): Promise<Uint8Array<ArrayBuffer>> {
  const out = new Blob([bytes]).stream().pipeThrough(stream);
  return new Uint8Array(await new Response(out).arrayBuffer());
}

const toBase64Url = (bytes: Uint8Array) =>
  btoa(Array.from(bytes, (b) => String.fromCharCode(b)).join(''))
    .replace(/\+/g, '-')
    .replace(/\//g, '_')
    .replace(/=+$/, '');

const fromBase64Url = (text: string) =>
  Uint8Array.from(atob(text.replace(/-/g, '+').replace(/_/g, '/')), (c) => c.charCodeAt(0));

/** A link to this page that opens the workspace. The whole workspace is in the link. */
export async function shareLink(ws: SharedWorkspace): Promise<string> {
  const json = new TextEncoder().encode(JSON.stringify({ name: ws.name, files: ws.files }));
  const packed = await pipe(json, new CompressionStream('deflate-raw'));
  const url = new URL(location.href);
  url.hash = prefix.slice(1) + toBase64Url(packed);
  return url.href;
}

/** The workspace in the page's own link, if it has one. */
export async function sharedFromLocation(): Promise<SharedWorkspace | null> {
  if (!location.hash.startsWith(prefix)) return null;
  try {
    const json = await pipe(fromBase64Url(location.hash.slice(prefix.length)), new DecompressionStream('deflate-raw'));
    const ws = JSON.parse(new TextDecoder().decode(json)) as SharedWorkspace;
    if (typeof ws.name !== 'string' || !Array.isArray(ws.files)) return null;
    const files = ws.files.filter((f) => typeof f.path === 'string' && typeof f.text === 'string');
    return { name: ws.name, files };
  } catch {
    return null;
  }
}
