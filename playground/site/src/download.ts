/** Bytes received so far and, when the server says, the bytes to expect. */
export interface Progress {
  readonly loaded: number;
  readonly total: number | null;
}

/**
 * Fetch several files and report the bytes received across all of them. A
 * response without a usable Content-Length counts as the bytes received so
 * far, so the total is exact once every file has arrived; it is unknown only
 * when no response states a length.
 */
export async function fetchAll(
  urls: readonly string[],
  onProgress: (p: Progress) => void,
): Promise<Uint8Array<ArrayBuffer>[]> {
  const loaded = urls.map(() => 0);
  const totals: (number | null)[] = urls.map(() => null);
  const report = () =>
    onProgress({
      loaded: loaded.reduce((a, b) => a + b, 0),
      total: totals.some((t) => t != null) ? totals.reduce<number>((a, t, j) => a + (t ?? loaded[j]!), 0) : null,
    });
  return Promise.all(
    urls.map(async (url, i) => {
      const response = await fetch(url);
      if (!response.ok || response.body == null) throw new Error(`${url} did not download (${response.status}).`);
      // A server that compresses on the way states the compressed length, so
      // the count of received bytes can pass it; then the total is unknown.
      const length = Number(response.headers.get('content-length'));
      const encoded = response.headers.get('content-encoding') != null;
      totals[i] = length > 0 && !encoded ? length : null;
      const chunks: Uint8Array[] = [];
      const reader = response.body.getReader();
      for (;;) {
        const { done, value } = await reader.read();
        if (done) break;
        chunks.push(value);
        loaded[i]! += value.byteLength;
        report();
      }
      const bytes = new Uint8Array(loaded[i]!);
      let offset = 0;
      for (const c of chunks) {
        bytes.set(c, offset);
        offset += c.byteLength;
      }
      return bytes;
    }),
  );
}

/**
 * Unpack a gzipped file. Some servers unpack it on the way, so this unpacks
 * only when the bytes still start with gzip's signature.
 */
export async function gunzip(bytes: Uint8Array<ArrayBuffer>): Promise<ArrayBuffer> {
  if (bytes[0] !== 0x1f || bytes[1] !== 0x8b) return bytes.buffer;
  const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream('gzip'));
  return new Response(stream).arrayBuffer();
}
