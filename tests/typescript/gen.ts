/**
 * Random typed programs of the TypeScript subset, from a seed.
 *
 * `checkTranslate.ts` translates them and compiles the output, and
 * `interpreter.test.ts` runs them in the interpreter and in Node. A program has
 * up to three interfaces, some of them declared as a `Record` over a literal
 * union, and up to three exported functions. A function calls
 * only the functions before it, so no program recurses.
 */

export type Signatures = {
  structs: ReadonlyArray<{ name: string; fields: ReadonlyArray<[string, Ty]> }>;
  functions: ReadonlyArray<{ name: string; params: ReadonlyArray<Ty>; ret: Ty }>;
};

export function random(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

export type Ty =
  | { k: 'bigint' }
  | { k: 'number' }
  | { k: 'boolean' }
  | { k: 'string' }
  | { k: 'nullable'; of: Ty }
  /** An optional parameter `p?: T`, only ever the last parameter. */
  | { k: 'optional'; of: Ty }
  | { k: 'array'; of: Ty }
  | { k: 'struct'; name: string };

type Var = { name: string; ty: Ty; mutable: boolean; owned: boolean };

export const BIGINT: Ty = { k: 'bigint' };
export const NUMBER: Ty = { k: 'number' };
export const BOOLEAN: Ty = { k: 'boolean' };
export const STRING: Ty = { k: 'string' };

export function same(a: Ty, b: Ty): boolean {
  return JSON.stringify(a) === JSON.stringify(b);
}

export function show(t: Ty): string {
  switch (t.k) {
    case 'bigint':
    case 'number':
    case 'boolean':
    case 'string':
      return t.k;
    case 'nullable':
      return `${show(t.of)} | null`;
    case 'optional':
      return `${show(t.of)} | undefined`;
    case 'array':
      return `ReadonlyArray<${show(t.of)}>`;
    case 'struct':
      return t.name;
  }
}

export class Gen {
  private readonly next: () => number;
  private structs: Array<{ name: string; fields: Array<[string, Ty]> }> = [];
  private enums: Array<{ name: string; members: Array<string> }> = [];
  /** The structures that are declared as `Record<K, T>`. */
  private records = new Set<string>();
  private functions: Array<{ name: string; params: Array<Ty>; ret: Ty }> = [];
  private counter = 0;

  constructor(seed: number) {
    this.next = random(seed);
  }

  private chance(p: number): boolean {
    return this.next() < p;
  }

  private pick<T>(xs: ReadonlyArray<T>): T {
    const x = xs[Math.floor(this.next() * xs.length)];
    if (x === undefined) {
      throw new Error('empty choice');
    }
    return x;
  }

  private fresh(prefix: string): string {
    this.counter++;
    return `${prefix}${this.counter}`;
  }

  private scalar(): Ty {
    return this.pick([BIGINT, BIGINT, NUMBER, NUMBER, BOOLEAN]);
  }

  private anyType(): Ty {
    const roll = this.next();
    if (roll < 0.45) {
      return this.scalar();
    }
    if (roll < 0.5) {
      return STRING;
    }
    if (roll < 0.65) {
      return { k: 'nullable', of: this.pick([BIGINT, NUMBER]) };
    }
    if (roll < 0.7 && this.structs.length > 0) {
      // A nullable structure, which `p?.f` reads.
      return { k: 'nullable', of: { k: 'struct', name: this.pick(this.structs).name } };
    }
    if (roll < 0.8 && this.structs.length > 0) {
      return { k: 'struct', name: this.pick(this.structs).name };
    }
    // An array of strings, which `split` gives.
    return { k: 'array', of: this.pick([BIGINT, NUMBER, STRING, ...this.structs.map((s): Ty => ({ k: 'struct', name: s.name }))]) };
  }

  /** An expression of type `t`, reading only `vars`. */
  expr(t: Ty, vars: ReadonlyArray<Var>, depth: number): string {
    const readable = vars.filter((v) => !v.owned);
    const ofType = readable.filter((v) => same(v.ty, t));
    const leaf = (): string => {
      if (ofType.length > 0 && this.chance(0.6)) {
        return this.pick(ofType).name;
      }
      switch (t.k) {
        case 'bigint':
          return this.pick(['0n', '1n', '7n', '0x1fn', '1_000n']);
        case 'number':
          return this.pick(['0', '1', '42', '1e3', '0x10', 'NaN', 'Infinity', '-Infinity']);
        case 'boolean':
          return this.pick(['true', 'false']);
        case 'string':
          // U+FFFF is above the code unit D83D that starts '😀', so the two
          // order one way by code unit, as JS does, and the other by code point.
          // White space and commas, which `trim` and `split` read.
          return this.pick(["''", "'a'", "'ab'", "'é'", "'😀'", "'\\uFFFF'", "' a,b '", "'\\u00A0x\\u2028'", "','"]);
        case 'nullable':
          return this.chance(0.5) ? 'null' : this.expr(t.of, vars, 0);
        case 'optional':
          return this.chance(0.5) ? 'undefined' : this.expr(t.of, vars, 0);
        case 'struct':
          return this.object(t.name, vars, 0);
        case 'array': {
          const any = readable.filter((v) => v.ty.k === 'array' && same(v.ty, t));
          if (any.length > 0 && this.chance(0.5)) return this.pick(any).name;
          // An array literal, with up to three elements.
          const n = this.pick([0, 1, 2, 3]);
          return `[${Array.from({ length: n }, () => this.expr(t.of, vars, 0)).join(', ')}]`;
        }
      }
    };
    if (depth <= 0 || this.chance(0.3)) {
      return leaf();
    }
    const d = depth - 1;
    const fields = this.fieldReads(t, readable);
    const calls = this.functions.filter((f) => same(f.ret, t));
    const options: Array<() => string> = [leaf];
    if (fields.length > 0) {
      options.push(() => this.pick(fields));
    }
    if (calls.length > 0) {
      options.push(() => {
        const f = this.pick(calls);
        // A call may leave out the optional parameter, which is last.
        const params = f.params.at(-1)?.k === 'optional' && this.chance(0.4) ? f.params.slice(0, -1) : f.params;
        return `${f.name}(${params.map((p) => this.expr(p, vars, d)).join(', ')})`;
      });
    }
    options.push(() => `(${this.test(vars, d)} ? ${this.expr(t, vars, d)} : ${this.expr(t, vars, d)})`);
    options.push(...this.callbacks(t, readable, vars, d));
    switch (t.k) {
      case 'bigint':
      case 'number':
        options.push(
          () => `${this.expr(t, vars, d)} ${this.pick(['+', '-', '*'])} ${this.expr(t, vars, d)}`,
          () => `-${this.expr(t, vars, d)}`,
          () => `(${this.expr(t, vars, d)})`,
        );
        // The length of a string and the index of a string in it, which count
        // UTF-16 code units.
        if (t.k === 'number') {
          // `/` and the functions of `Math` that the model has. A division
          // by zero gives an infinity or `NaN`, which the values check too.
          options.push(
            () => `${this.expr(t, vars, d)} / ${this.expr(t, vars, d)}`,
            () => `Math.${this.pick(['floor', 'ceil', 'trunc', 'round', 'abs'])}(${this.expr(t, vars, d)})`,
            // The bitwise operators, on ToInt32 and ToUint32 of each operand.
            () => `(${this.expr(t, vars, d)} ${this.pick(['&', '|', '^', '<<', '>>', '>>>'])} ${this.expr(t, vars, d)})`,
            () => `~${this.expr(t, vars, d)}`,
            () => {
              const count = this.pick([0, 1, 2, 3]);
              const args = Array.from({ length: count }, () => this.expr(t, vars, d));
              return `Math.${this.pick(['min', 'max'])}(${args.join(', ')})`;
            },
          );
          options.push(
            () => `(${this.expr(STRING, vars, d)}).length`,
            () => `(${this.expr(STRING, vars, d)}).indexOf(${this.expr(STRING, vars, d)})`,
          );
        }
        // An element of an array, by an index that is a number literal,
        // which checks the interpreter's rule for `xs[i]` against Node. The
        // index `2` is past the end, which is `undefined`. The translator
        // refuses an index of anything but a tuple, so it comes only
        // sometimes.
        if (this.chance(0.1)) {
          options.push(
            () => `[${this.expr(t, vars, d)}, ${this.expr(t, vars, d)}][${this.pick(['0', '1', '2', '0x1'])}]`,
          );
        }
        {
          // `x ?? e`: `x` unless it is `null`.
          const nullable = readable.filter((v) => (v.ty.k === 'nullable' || v.ty.k === 'optional') && same(v.ty.of, t));
          if (nullable.length > 0) {
            options.push(() => `${this.pick(nullable).name} ?? ${this.expr(t, vars, d)}`);
          }
          // `p?.f ?? e` and `p?.f.g ?? e`, on a nullable structure with a
          // field of type `t`, or a field of a structure whose field has it.
          const chains = readable.flatMap((v) => {
            const of = v.ty.k === 'nullable' ? v.ty.of : undefined;
            const s = of?.k === 'struct' ? this.structs.find((x) => x.name === of.name) : undefined;
            const direct = (s?.fields ?? []).filter(([, ft]) => same(ft, t)).map(([f]) => `${v.name}?.${f}`);
            const nested = (s?.fields ?? []).flatMap(([f, ft]) => {
              const inner = ft.k === 'struct' ? this.structs.find((x) => x.name === ft.name) : undefined;
              return (inner?.fields ?? []).filter(([, gt]) => same(gt, t)).map(([g]) => `${v.name}?.${f}.${g}`);
            });
            return [...direct, ...nested];
          });
          if (chains.length > 0) {
            options.push(() => `(${this.pick(chains)} ?? ${this.expr(t, vars, d)})`);
          }
        }
        if (t.k === 'bigint') {
          // Both translators accept a nonzero literal divisor only.
          options.push(() => `${this.expr(t, vars, d)} ${this.pick(['/', '%'])} ${this.pick(['2n', '-3n', '(7n)', '-(5n)', '0n', this.expr(t, vars, 0)])}`);
          // The bitwise operators, and `**` with a literal exponent, which
          // both translators require. The base is in parentheses, because
          // `-a ** 2n` is a syntax error. A shift count and an exponent stay
          // small, so that the values do too: JS throws a RangeError when a
          // bigint gets too large, and Lean panics. So the shift is in
          // parentheses too, or `a >> -2n - b` would shift by `-2n - b`.
          options.push(
            () => `${this.expr(t, vars, d)} ${this.pick(['&', '|', '^'])} ${this.expr(t, vars, d)}`,
            () => `~${this.expr(t, vars, d)}`,
            () => `((${this.expr(t, vars, d)}) ** ${this.pick(['0n', '2n', '(3n)', '-1n'])})`,
            () => `(${this.expr(t, vars, d)} ${this.pick(['<<', '>>'])} ${this.pick(['1n', '-2n', '(5n)', '70n', `(${this.expr(t, vars, 0)} & 7n)`])})`,
          );
        }
        break;
      case 'boolean': {
        const nullable = readable.filter((v) => v.ty.k === 'nullable');
        options.push(
          () => {
            const u = this.pick([BIGINT, NUMBER]);
            return `${this.expr(u, vars, d)} ${this.pick(['<', '<=', '>', '>=', '===', '!=='])} ${this.expr(u, vars, d)}`;
          },
          () => `${this.expr(BOOLEAN, vars, d)} ${this.pick(['&&', '||'])} ${this.expr(BOOLEAN, vars, d)}`,
          () => `!${this.expr(BOOLEAN, vars, d)}`,
          // Not two literals: tsc refuses \`true === false\` (TS2367), and narrows
          // oddly in the branch \`true === true\` makes impossible.
          () => {
            const flags = readable.filter((v) => v.ty.k === 'boolean');
            return flags.length > 0 ? `${this.pick(flags).name} === ${this.expr(BOOLEAN, vars, d)}` : 'true';
          },
          () => `Number.${this.pick(['isNaN', 'isFinite', 'isSafeInteger', 'isInteger'])}(${this.expr(NUMBER, vars, d)})`,
          // A test of one string in another, by code units.
          () => `(${this.expr(STRING, vars, d)}).${this.pick(['startsWith', 'endsWith', 'includes'])}(${this.expr(STRING, vars, d)})`,
          // A test of the pieces that `split` gives.
          () => {
            const p = this.fresh('c');
            return `(${this.expr(STRING, vars, d)}).split(${this.expr(STRING, vars, d)}).some((${p}) => ${p} === ${this.expr(STRING, vars, 0)})`;
          },
        );
        // `typeof` on a value of any type, which checks the interpreter's rule
        // against Node. The translator refuses it here, so it comes only
        // sometimes, and most programs still translate.
        if (this.chance(0.3)) {
          options.push(
            () =>
              `typeof (${this.expr(this.anyType(), vars, d)}) ${this.pick(['===', '!=='])} ` +
              `'${this.pick(['bigint', 'number', 'boolean', 'string', 'object'])}'`,
          );
        }
        // Not two literals: tsc refuses `'a' === 'b'` (TS2367). Strings
        // order by their code units.
        const strings = [...readable.filter((v) => v.ty.k === 'string').map((v) => v.name), ...this.fieldReads(STRING, readable)];
        if (strings.length > 0) {
          options.push(() => `${this.pick(strings)} ${this.pick(['===', '!==', '<', '<=', '>', '>='])} ${this.expr(STRING, vars, d)}`);
        }
        if (nullable.length > 0) {
          options.push(() => {
            const v = this.pick(nullable);
            const narrowed = vars.map((x) => (x.name === v.name && x.ty.k === 'nullable' ? { ...x, ty: x.ty.of } : x));
            // `==` and `!=` test for `null` as `===` and `!==` do, because the
            // subset has no `undefined`.
            return this.chance(0.5)
              ? `${v.name} ${this.pick(['===', '=='])} null || ${this.expr(BOOLEAN, narrowed, d)}`
              : `${v.name} ${this.pick(['!==', '!='])} null && ${this.expr(BOOLEAN, narrowed, d)}`;
          }, () => `${this.pick(nullable).name} ${this.pick(['===', '!==', '==', '!='])} null`);
        }
        break;
      }
      case 'string':
        // `+` with a string on either side, which converts the other operand
        // with ToString. The operands are in parentheses, so that a
        // conditional inside one does not take the `+` into its test.
        options.push(() => {
          const other = this.expr(this.pick([STRING, BIGINT, BOOLEAN]), vars, d);
          const s = this.expr(STRING, vars, d);
          return this.chance(0.5) ? `(${s}) + (${other})` : `(${other}) + (${s})`;
        });
        // `trim`, `trimStart` and `trimEnd`, which remove white space.
        options.push(() => `(${this.expr(STRING, vars, d)}).${this.pick(['trim', 'trimStart', 'trimEnd'])}()`);
        // `typeof` on a value of any type. The translator accepts it only in
        // the test of an `if` on a union of primitive types, but the
        // interpreter runs it anywhere, so this and the comparison of
        // booleans above check its rule against Node.
        options.push(() => `typeof (${this.expr(this.anyType(), vars, d)})`);
        // A member of a string enum, which is a string. The translator
        // refuses it where a `string` is expected, but the interpreter reads
        // it from the enum's object, so this checks that rule against Node.
        if (this.enums.length > 0) {
          options.push(() => {
            const e = this.pick(this.enums);
            return `${e.name}.${this.pick(e.members)}`;
          });
        }
        break;
      case 'array':
        // `split` with a string separator gives an array of strings.
        if (t.of.k === 'string') {
          options.push(() => `(${this.expr(STRING, vars, d)}).split(${this.expr(STRING, vars, d)})`);
        }
        break;
      default:
        break;
    }
    return this.pick(options)();
  }

  /** Calls of `map`, `filter`, `some`, `every` and `find` on an array in
   * scope that give a value of type `t`. The callback's parameter is a fresh
   * name, which its body may read with the other names in scope; a callback
   * of `map` may also take the index, a number. The body is in parentheses,
   * so that an object literal is not read as a block. */
  private callbacks(t: Ty, readable: ReadonlyArray<Var>, vars: ReadonlyArray<Var>, depth: number): Array<() => string> {
    const arrays = readable.flatMap((v) => (v.ty.k === 'array' ? [{ name: v.name, elem: v.ty.of }] : []));
    if (arrays.length === 0) return [];
    const call = (method: string, recv: { name: string; elem: Ty }, body: (inner: ReadonlyArray<Var>) => string): string => {
      const p = this.fresh('c');
      const inner = [...vars, { name: p, ty: recv.elem, mutable: false, owned: false }];
      return `${recv.name}.${method}(${p} => (${body(inner)}))`;
    };
    const mapIdx = (recv: { name: string; elem: Ty }, body: (inner: ReadonlyArray<Var>) => string): string => {
      const p = this.fresh('c');
      const i = this.fresh('i');
      const inner = [
        ...vars,
        { name: i, ty: NUMBER, mutable: false, owned: false },
        { name: p, ty: recv.elem, mutable: false, owned: false },
      ];
      return `${recv.name}.map((${p}, ${i}) => (${body(inner)}))`;
    };
    const options: Array<() => string> = [];
    switch (t.k) {
      case 'boolean': {
        options.push(() => call(this.pick(['some', 'every']), this.pick(arrays), (inner) => this.expr(BOOLEAN, inner, depth)));
        // `includes` on primitives, which SameValueZero compares by value.
        // A number array may hold `NaN`, which `includes` finds.
        const primitive = arrays.filter((a) => ['bigint', 'number', 'boolean', 'string'].includes(a.elem.k));
        if (primitive.length > 0) {
          options.push(() => {
            const recv = this.pick(primitive);
            return `${recv.name}.includes(${this.expr(recv.elem, vars, depth)})`;
          });
        }
        break;
      }
      case 'array': {
        const of = t.of;
        options.push(() => call('map', this.pick(arrays), (inner) => this.expr(of, inner, depth)));
        options.push(() => mapIdx(this.pick(arrays), (inner) => this.expr(of, inner, depth)));
        const same_ = arrays.filter((a) => same(a.elem, of));
        if (same_.length > 0) {
          options.push(() => call('filter', this.pick(same_), (inner) => this.expr(BOOLEAN, inner, depth)));
          // A slice with integer literals, from the start or from the end.
          options.push(() => {
            const bounds = this.pick(['', '1', '-2', '0, 2', '1, -1', '-3, -1', '2, 1']);
            return `${this.pick(same_).name}.slice(${bounds})`;
          });
          // A spread of one array or two, with elements around them.
          options.push(() => {
            const parts = [`...${this.pick(same_).name}`];
            if (this.chance(0.5)) parts.push(this.expr(of, vars, 0));
            if (this.chance(0.5)) parts.unshift(this.expr(of, vars, 0));
            if (this.chance(0.5)) parts.push(`...${this.pick(same_).name}`);
            return `[${parts.join(', ')}]`;
          });
        }
        break;
      }
      case 'bigint':
      case 'number': {
        // `find` gives `undefined` when no element passes, and `??` gives the
        // default then.
        const same_ = arrays.filter((a) => same(a.elem, t));
        if (same_.length > 0) {
          options.push(() => `(${call(this.pick(['find', 'findLast']), this.pick(same_), (inner) => this.expr(BOOLEAN, inner, depth))} ?? ${this.expr(t, vars, depth)})`);
          // An element at an index, which is `undefined` outside the array:
          // a literal, any number, or a literal counted from the end.
          options.push(() => {
            const recv = this.pick(same_).name;
            const index = this.pick([
              () => `${recv}[${this.pick([0, 1, 2])}]`,
              () => `${recv}[${this.expr(NUMBER, vars, depth)}]`,
              () => `${recv}.at(${this.pick([0, 1, -1, -2])})`,
            ])();
            return `(${index} ?? ${this.expr(t, vars, depth)})`;
          });
        }
        // The length of an array is a number.
        if (t.k === 'number') options.push(() => `${this.pick(arrays).name}.length`);
        // `findIndex` gives the index of the first element that passes, a
        // number, or -1.
        if (t.k === 'number') {
          options.push(() => call('findIndex', this.pick(arrays), (inner) => this.expr(BOOLEAN, inner, depth)));
        }
        // `reduce` with an initial value of type `t`: the body reads the value
        // so far, the element and the names in scope.
        options.push(() => {
          const recv = this.pick(arrays);
          const acc = this.fresh('a');
          const p = this.fresh('c');
          const inner = [...vars, { name: acc, ty: t, mutable: false, owned: false },
            { name: p, ty: recv.elem, mutable: false, owned: false }];
          return `${recv.name}.reduce((${acc}, ${p}) => (${this.expr(t, inner, depth)}), ${this.expr(t, vars, depth)})`;
        });
        break;
      }
      default:
        break;
    }
    return options;
  }

  /** A condition that is not a literal. With a literal test, such as
   * `true ? a : b`, tsc drops its null narrowing in the impossible branch and
   * reports an error there; that is a quirk of tsc on dead code, not a type
   * error the translators need to agree on. */
  private test(vars: ReadonlyArray<Var>, depth: number): string {
    const flags = vars.filter((v) => !v.owned && v.ty.k === 'boolean');
    if (flags.length > 0 && this.chance(0.5)) {
      return this.pick(flags).name;
    }
    // Strings order by their code units, so a test may compare a string
    // local with a string.
    const strings = vars.filter((v) => !v.owned && v.ty.k === 'string');
    const u = strings.length > 0 && this.chance(0.3) ? STRING : this.pick([BIGINT, NUMBER]);
    const ordered = vars.filter((v) => !v.owned && same(v.ty, u));
    const left = ordered.length > 0 ? this.pick(ordered).name : this.expr(u, vars, depth);
    return `${left} ${this.pick(['<', '<=', '>', '>='])} ${this.expr(u, vars, depth)}`;
  }

  private fieldReads(t: Ty, vars: ReadonlyArray<Var>): Array<string> {
    const reads: Array<string> = [];
    for (const v of vars) {
      if (v.ty.k !== 'struct') {
        continue;
      }
      const name = v.ty.name;
      const s = this.structs.find((x) => x.name === name);
      for (const [field, ty] of s?.fields ?? []) {
        if (same(ty, t)) {
          reads.push(this.records.has(name) && this.chance(0.5) ? `${v.name}['${field}']` : `${v.name}.${field}`);
        }
      }
    }
    return reads;
  }

  private object(name: string, vars: ReadonlyArray<Var>, depth: number): string {
    const s = this.structs.find((x) => x.name === name);
    // A spread of a value of the same interface, which then sets some of its
    // required fields in their places.
    const bases = vars.filter((x) => !x.owned && x.ty.k === 'struct' && x.ty.name === name);
    if (bases.length > 0 && this.chance(0.4)) {
      const set = (s?.fields ?? []).filter(([, ty]) => ty.k !== 'optional' && this.chance(0.5));
      const parts = set.map(([field, ty]) => `${field}: ${this.expr(ty, vars, depth)}`);
      return `{ ${[`...${this.pick(bases).name}`, ...parts].join(', ')} }`;
    }
    const parts = (s?.fields ?? []).map(([field, ty]) => {
      const v = vars.find((x) => x.name === field && same(x.ty, ty) && !x.owned);
      return v !== undefined && this.chance(0.5) ? field : `${field}: ${this.expr(ty, vars, depth)}`;
    });
    return `{ ${parts.join(', ')} }`;
  }

  private body(vars: Array<Var>, ret: Ty, depth: number, inLoop: boolean): Array<string> {
    const lines: Array<string> = [];
    const count = 1 + Math.floor(this.next() * 3);
    for (let i = 0; i < count; i++) {
      const roll = this.next();
      const lets = vars.filter((v) => v.mutable);
      const patternArrays = vars.filter((v) =>
        v.ty.k === 'array' && !v.owned && v.ty.of.k !== 'nullable' && v.ty.of.k !== 'optional');
      if (roll < 0.08 && patternArrays.length > 0) {
        // An array pattern: each place is optional, `undefined` past the end,
        // and the rest is an array of the values after the places.
        const xs = this.pick(patternArrays);
        if (xs.ty.k === 'array') {
          const of = xs.ty.of;
          const places = Array.from({ length: 1 + Math.floor(this.next() * 3) }, () =>
            this.chance(0.75) ? this.fresh('d') : '');
          // A hole may not end the pattern.
          if (places[places.length - 1] === '') places[places.length - 1] = this.fresh('d');
          const rest = this.chance(0.4) ? this.fresh('r') : undefined;
          lines.push(`const [${places.join(', ')}${rest !== undefined ? `, ...${rest}` : ''}] = ${xs.name};`);
          for (const p of places) {
            if (p !== '') vars.push({ name: p, ty: { k: 'optional', of }, mutable: false, owned: false });
          }
          if (rest !== undefined) vars.push({ name: rest, ty: { k: 'array', of }, mutable: false, owned: false });
        }
      } else if (roll < 0.3) {
        const t = this.pick([BIGINT, NUMBER, BOOLEAN, STRING, { k: 'nullable', of: BIGINT } as Ty,
          ...(this.structs.length > 0 ? [{ k: 'struct', name: this.pick(this.structs).name } as Ty] : [])]);
        const name = this.fresh('v');
        const mutable = this.chance(0.6);
        const value = this.expr(t, vars, 2);
        // A bare `null` gives the local the type `null`, which Tolean refuses.
        const annotate = t.k === 'struct' || value === 'null' || this.chance(0.2);
        lines.push(`${mutable ? 'let' : 'const'} ${name}${annotate ? `: ${show(t)}` : ''} = ${value};`);
        vars.push({ name, ty: t, mutable, owned: false });
      } else if (roll < 0.5 && lets.length > 0) {
        const v = this.pick(lets);
        // `x ??= e` assigns only when `x` is null.
        // `s += e` on a string joins `e` after ToString.
        const op = v.ty.k === 'bigint' || v.ty.k === 'number' ? this.pick(['=', '+=', '-=', '*='])
          : v.ty.k === 'nullable' ? this.pick(['=', '??='])
          : v.ty.k === 'string' ? this.pick(['=', '+=']) : '=';
        const valueTy = op === '+=' && v.ty.k === 'string' ? this.pick([STRING, BIGINT, BOOLEAN]) : v.ty;
        lines.push(`${v.name} ${op} ${this.expr(valueTy, vars, 2)};`);
      } else if (roll < 0.65 && depth > 0 && lets.length > 0) {
        const v = this.pick(lets);
        lines.push(`if (${this.test(vars, 2)}) {`, `  ${v.name} = ${this.expr(v.ty, vars, 1)};`, '}');
      } else if (roll < 0.8 && depth > 0) {
        const arrays = vars.filter((v) => v.ty.k === 'array' && !v.owned);
        const target = lets.length > 0 ? this.pick(lets) : undefined;
        if (target !== undefined && (arrays.length === 0 || this.chance(0.4))) {
          // A counted loop, up to the length of an array that the body does
          // not assign, or up to a small number.
          const i = this.fresh('i');
          const bounds = arrays.filter((v) => v.name !== target.name);
          const bound = bounds.length > 0 && this.chance(0.6) ? `${this.pick(bounds).name}.length`
            : String(this.pick([0, 1, 2, 3, 5]));
          const update = this.pick([`${i}++`, `++${i}`, `${i} += 1`]);
          const inner = [...vars, { name: i, ty: NUMBER, mutable: false, owned: false }];
          const assign = `${target.name} = ${this.expr(target.ty, inner, 1)};`;
          const jump = this.next();
          const body = jump < 0.2 ? [`  if (${this.test(inner, 1)}) continue;`, `  ${assign}`]
            : jump < 0.3 ? [`  if (${this.test(inner, 1)}) break;`, `  ${assign}`]
            : jump < 0.4 ? [`  if (${this.test(inner, 1)}) return ${this.expr(ret, inner, 1)};`, `  ${assign}`]
            : [`  ${assign}`];
          lines.push(`for (let ${i} = ${this.pick([0, 0, 1, -1, 2])}; ${i} < ${bound}; ${update}) {`, ...body, '}');
        } else if (arrays.length > 0 && target !== undefined) {
          const xs = this.pick(arrays);
          if (xs.ty.k === 'array') {
            // Sometimes a loop over a literal of arrays, whose head is an
            // array pattern: the first value, which is optional, and the rest.
            const of = xs.ty.of;
            const pattern = of.k !== 'nullable' && of.k !== 'optional' && this.chance(0.6);
            const element = this.fresh('e');
            const restName = this.fresh('q');
            const inner = pattern
              ? [...vars, { name: element, ty: { k: 'optional', of } as Ty, mutable: false, owned: false },
                { name: restName, ty: { k: 'array', of } as Ty, mutable: false, owned: false }]
              : [...vars, { name: element, ty: xs.ty.of, mutable: false, owned: false }];
            const head = pattern ? `[${element}, ...${restName}]` : element;
            const iterable = pattern ? `[${xs.name}, ${this.pick(arrays.filter((a) => same(a.ty, xs.ty))).name}]` : xs.name;
            const assign = `${target.name} = ${this.expr(target.ty, inner, 1)};`;
            // A `continue` skips the assignment for some elements, a `break`
            // ends the loop there, and a `return` ends the function.
            const jump = this.next();
            const body = jump < 0.2 ? [`  if (${this.test(inner, 1)}) continue;`, `  ${assign}`]
              : jump < 0.3 ? [`  if (${this.test(inner, 1)}) {`, `    ${assign}`, '    continue;', '  }', `  ${assign}`]
              : jump < 0.4 ? [`  if (${this.test(inner, 1)}) break;`, `  ${assign}`]
              : jump < 0.5 ? [`  if (${this.test(inner, 1)}) return ${this.expr(ret, inner, 1)};`, `  ${assign}`]
              : [`  ${assign}`];
            lines.push(`for (const ${head} of ${iterable}) {`, ...body, '}');
          }
        }
      } else if (roll < 0.85 && depth > 0) {
        // An array that the function owns, with a push; a later loop can read it.
        const t = this.pick([BIGINT, NUMBER]);
        const name = this.fresh('o');
        const start = this.chance(0.5) ? this.expr(t, vars, 0) : '';
        lines.push(`const ${name}: Array<${show(t)}> = [${start}];`, `${name}.push(${this.expr(t, vars, 1)});`);
        vars.push({ name, ty: { k: 'array', of: t }, mutable: false, owned: false });
      } else if (roll < 0.89 && depth > 0 && this.chance(0.5)) {
        // A set that the function owns, with adds and deletes, read as a map is.
        const elem = this.pick([BIGINT, STRING, BOOLEAN]);
        const name = this.fresh('s');
        // Sometimes with values to start with, which may repeat.
        const start = this.chance(0.3) ? `[${this.expr(elem, vars, 1)}, ${this.expr(elem, vars, 1)}]` : '';
        lines.push(`const ${name} = new Set<${show(elem)}>(${start});`);
        const changes = 1 + Math.floor(this.next() * 4);
        for (let j = 0; j < changes; j++) {
          lines.push(`${name}.${this.chance(0.75) ? 'add' : 'delete'}(${this.expr(elem, vars, 1)});`);
        }
        const has = this.fresh('h');
        const size = this.fresh('n');
        lines.push(`const ${has} = ${name}.has(${this.expr(elem, vars, 1)});`, `const ${size} = ${name}.size;`);
        vars.push({ name: has, ty: BOOLEAN, mutable: false, owned: false },
          { name: size, ty: NUMBER, mutable: false, owned: false });
        if (this.chance(0.5)) {
          // A loop over the set, in the order of insertion.
          const acc = this.fresh('a');
          const x = this.fresh('e');
          const inner = [...vars, { name: x, ty: elem, mutable: false, owned: false }];
          lines.push(`let ${acc} = ${this.expr(elem, vars, 1)};`, `for (const ${x} of ${name}) {`,
            `  ${acc} = ${this.expr(elem, inner, 1)};`, '}');
          vars.push({ name: acc, ty: elem, mutable: true, owned: false });
        }
      } else if (roll < 0.89 && depth > 0) {
        // A map that the function owns, with sets and deletes. Code may read
        // it only through get, has and size, so the reads go into locals.
        const key = this.pick([BIGINT, STRING, BOOLEAN]);
        const value = this.pick([BIGINT, NUMBER, STRING]);
        const name = this.fresh('m');
        const start = this.chance(0.3)
          ? `[[${this.expr(key, vars, 1)}, ${this.expr(value, vars, 1)}], [${this.expr(key, vars, 1)}, ${this.expr(value, vars, 1)}]]`
          : '';
        lines.push(`const ${name} = new Map<${show(key)}, ${show(value)}>(${start});`);
        const changes = 1 + Math.floor(this.next() * 4);
        for (let j = 0; j < changes; j++) {
          lines.push(this.chance(0.75)
            ? `${name}.set(${this.expr(key, vars, 1)}, ${this.expr(value, vars, 1)});`
            : `${name}.delete(${this.expr(key, vars, 1)});`);
        }
        const got = this.fresh('g');
        const has = this.fresh('h');
        const size = this.fresh('n');
        lines.push(
          `const ${got} = ${name}.get(${this.expr(key, vars, 1)}) ?? ${this.expr(value, vars, 1)};`,
          `const ${has} = ${name}.has(${this.expr(key, vars, 1)});`,
          `const ${size} = ${name}.size;`,
        );
        vars.push({ name: got, ty: value, mutable: false, owned: false },
          { name: has, ty: BOOLEAN, mutable: false, owned: false },
          { name: size, ty: NUMBER, mutable: false, owned: false });
        if (this.chance(0.5)) {
          // A loop over the entries, each a [key, value] pair.
          const [t, index] = this.chance(0.5) ? [key, 0] : [value, 1];
          const acc = this.fresh('a');
          const e = this.fresh('e');
          lines.push(`let ${acc} = ${this.expr(t, vars, 1)};`, `for (const ${e} of ${name}) {`,
            `  ${acc} = ${e}[${index}];`, '}');
          vars.push({ name: acc, ty: t, mutable: true, owned: false });
        }
      } else if (roll < 0.93 && depth > 0 && !inLoop) {
        lines.push(...this.switchStatement(vars, ret, lets));
      } else if (roll < 0.97 && !inLoop) {
        // An early exit with an error, which a caller passes on.
        lines.push(`if (${this.test(vars, 2)}) throw new Error(${this.pick(["'too big'", "''", "'é'"])});`);
      } else if (!inLoop && this.chance(0.3)) {
        // Rarely, something outside the subset or ill-typed, to check that both refuse.
        lines.push(this.pick([
          `const bad${this.counter} = 5n / 2n;`,
          `let w${this.counter} = 1; w${this.counter} = true;`,
          `const q${this.counter} = ${vars[0]?.name ?? 'x'}.missing;`,
        ]));
      }
    }
    lines.push(`return ${this.expr(ret, vars, 2)};`);
    return lines;
  }

  /** A `switch` on a scalar. The translator takes only a switch on a tag,
   * so this one is for the interpreter test: its clauses assign a `let`,
   * then return, break, or run into the next clause, and the `default` can stand
   * anywhere, where the interpreter leaves the subset unless it is last. */
  private switchStatement(vars: ReadonlyArray<Var>, ret: Ty, lets: ReadonlyArray<Var>): Array<string> {
    const t = this.pick([BIGINT, NUMBER, STRING, BOOLEAN]);
    const clauses: Array<string> = Array.from({ length: 1 + Math.floor(this.next() * 3) }, () =>
      `  case ${this.expr(t, vars, 0)}:`);
    if (this.chance(0.6)) {
      clauses.splice(Math.floor(this.next() * (clauses.length + 1)), 0, '  default:');
    }
    const lines = [`switch (${this.expr(t, vars, 1)}) {`];
    for (const head of clauses) {
      lines.push(head);
      if (lets.length > 0 && this.chance(0.6)) {
        const v = this.pick(lets);
        lines.push(`    ${v.name} = ${this.expr(v.ty, vars, 1)};`);
      }
      if (this.chance(0.5)) {
        lines.push(`    return ${this.expr(ret, vars, 1)};`);
      } else if (this.chance(0.5)) {
        lines.push('    break;');
      }
    }
    lines.push('}');
    return lines;
  }

  /** The interfaces and the functions of the program, in order. */
  signatures(): Signatures {
    return { structs: this.structs, functions: this.functions };
  }

  program(): string {
    const out: Array<string> = [];
    if (this.chance(0.3)) {
      // A string enum. Two members may have one string, which the
      // translator refuses and the interpreter reads as JS does.
      const members = ['A', 'B', 'default'].slice(0, 1 + Math.floor(this.next() * 3));
      const values = members.map(() => this.pick(['a', 'b', 'c']));
      const exported = this.chance(0.5) ? 'export ' : '';
      out.push(`${exported}enum E0 {`, ...members.map((m, i) => `  ${m} = '${values[i]}',`), '}');
      this.enums.push({ name: 'E0', members });
    }
    const structCount = Math.floor(this.next() * 3);
    for (let i = 0; i < structCount; i++) {
      const name = `S${i}`;
      const fields: Array<[string, Ty]> = [];
      const n = 1 + Math.floor(this.next() * 3);
      const types: ReadonlyArray<Ty> = [BIGINT, NUMBER, BOOLEAN, STRING, { k: 'nullable', of: NUMBER }];
      if (this.chance(0.3)) {
        // A Record over a literal union: a structure whose fields all have
        // one type, which `r['f0']` reads too.
        const t = this.pick(types);
        for (let j = 0; j < n; j++) {
          fields.push([`f${j}`, t]);
        }
        out.push(`type K${i} = ${fields.map(([f]) => `'${f}'`).join(' | ')};`, `type ${name} = Record<K${i}, ${show(t)}>;`);
        this.records.add(name);
      } else {
        for (let j = 0; j < n; j++) {
          fields.push([`f${j}`, this.pick(types)]);
        }
        out.push(`interface ${name} {`, ...fields.map(([f, t]) => `  readonly ${f}: ${show(t)};`), '}');
      }
      this.structs.push({ name, fields });
    }
    const fnCount = 1 + Math.floor(this.next() * 3);
    for (let i = 0; i < fnCount; i++) {
      const name = `fn${i}`;
      const params: Array<Ty> = [];
      const vars: Array<Var> = [];
      const pc = Math.floor(this.next() * 4);
      for (let j = 0; j < pc; j++) {
        const t = this.anyType();
        params.push(t);
        vars.push({ name: `p${j}`, ty: t, mutable: false, owned: false });
      }
      // Sometimes an optional parameter last, which `??` reads and a test of
      // `undefined` narrows.
      if (this.chance(0.25)) {
        const t: Ty = { k: 'optional', of: this.pick([BIGINT, NUMBER, BOOLEAN]) };
        params.push(t);
        vars.push({ name: `p${pc}`, ty: t, mutable: false, owned: false });
      }
      // Sometimes nullable, so that a call can return `null`.
      const ret = this.chance(0.3) && this.structs.length > 0
        ? ({ k: 'struct', name: this.pick(this.structs).name } as Ty)
        : this.chance(0.15) ? ({ k: 'nullable', of: this.pick([BIGINT, NUMBER]) } as Ty) : this.scalar();
      const signature = vars
        .map((v) => (v.ty.k === 'optional' ? `${v.name}?: ${show(v.ty.of)}` : `${v.name}: ${show(v.ty)}`))
        .join(', ');
      const nullable = vars.filter((v) => v.ty.k === 'nullable');
      const lines: Array<string> = [];
      const optional = vars.find((v) => v.ty.k === 'optional');
      if (optional !== undefined && this.chance(0.5)) {
        // `if (x === undefined) return …;` narrows `x` in the rest of the body.
        const test = this.pick([`${optional.name} === undefined`, `undefined === ${optional.name}`]);
        lines.push(`if (${test}) {`, `  return ${this.expr(ret, vars, 1)};`, '}');
        if (optional.ty.k === 'optional') {
          optional.ty = optional.ty.of;
        }
      }
      if (nullable.length > 0 && this.chance(0.5)) {
        // `if (x === null) return …;` narrows `x` in the rest of the body.
        const v = this.pick(nullable);
        lines.push(`if (${v.name} === null) {`, `  return ${this.expr(ret, vars, 1)};`, '}');
        if (v.ty.k === 'nullable') {
          v.ty = v.ty.of;
        }
      }
      lines.push(...this.body(vars, ret, 2, false));
      out.push(`export function ${name}(${signature}): ${show(ret)} {`, ...lines.map((l) => `  ${l}`), '}');
      this.functions.push({ name, params, ret });
    }
    return out.join('\n') + '\n';
  }
}
