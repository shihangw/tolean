class NotFound extends Error {}
export class TooMany extends Error {
  constructor(readonly limit: bigint, extra: string) {
    super("too many: " + extra);
  }
}
class Plain extends Error { constructor(message: string) { super(message) } }
