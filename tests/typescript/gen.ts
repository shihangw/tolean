/**
 * Random typed programs of the TypeScript subset, from a seed.
 *
 * `checkTranslate.ts` translates them and compiles the output, and
 * `interpreter.test.ts` runs them in the interpreter and in Node. A program has
 * up to three interfaces and up to three exported functions. A function calls
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
    case 'array':
      return `ReadonlyArray<${show(t.of)}>`;
    case 'struct':
      return t.name;
  }
}

export class Gen {
  private readonly next: () => number;
  private structs: Array<{ name: string; fields: Array<[string, Ty]> }> = [];
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
    if (roll < 0.8 && this.structs.length > 0) {
      return { k: 'struct', name: this.pick(this.structs).name };
    }
    return { k: 'array', of: this.pick([BIGINT, NUMBER, ...this.structs.map((s): Ty => ({ k: 'struct', name: s.name }))]) };
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
          return this.pick(["''", "'a'", "'ab'", "'é'", "'😀'"]);
        case 'nullable':
          return this.chance(0.5) ? 'null' : this.expr(t.of, vars, 0);
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
        return `${f.name}(${f.params.map((p) => this.expr(p, vars, d)).join(', ')})`;
      });
    }
    options.push(() => `(${this.test(vars, d)} ? ${this.expr(t, vars, d)} : ${this.expr(t, vars, d)})`);
    switch (t.k) {
      case 'bigint':
      case 'number':
        options.push(
          () => `${this.expr(t, vars, d)} ${this.pick(['+', '-', '*'])} ${this.expr(t, vars, d)}`,
          () => `-${this.expr(t, vars, d)}`,
          () => `(${this.expr(t, vars, d)})`,
        );
        {
          // `x ?? e`, which the interpreter runs and the translator refuses.
          const nullable = readable.filter((v) => v.ty.k === 'nullable' && same(v.ty.of, t));
          if (nullable.length > 0) {
            options.push(() => `${this.pick(nullable).name} ?? ${this.expr(t, vars, d)}`);
          }
        }
        if (t.k === 'bigint') {
          // Both translators accept a nonzero literal divisor only.
          options.push(() => `${this.expr(t, vars, d)} ${this.pick(['/', '%'])} ${this.pick(['2n', '-3n', '(7n)', '-(5n)', '0n', this.expr(t, vars, 0)])}`);
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
          () => `Number.${this.pick(['isNaN', 'isFinite', 'isSafeInteger'])}(${this.expr(NUMBER, vars, d)})`,
        );
        // Not two literals: tsc refuses `'a' === 'b'` (TS2367).
        const strings = [...readable.filter((v) => v.ty.k === 'string').map((v) => v.name), ...this.fieldReads(STRING, readable)];
        if (strings.length > 0) {
          options.push(() => `${this.pick(strings)} ${this.pick(['===', '!=='])} ${this.expr(STRING, vars, d)}`);
        }
        if (nullable.length > 0) {
          options.push(() => {
            const v = this.pick(nullable);
            const narrowed = vars.map((x) => (x.name === v.name && x.ty.k === 'nullable' ? { ...x, ty: x.ty.of } : x));
            return this.chance(0.5)
              ? `${v.name} === null || ${this.expr(BOOLEAN, narrowed, d)}`
              : `${v.name} !== null && ${this.expr(BOOLEAN, narrowed, d)}`;
          }, () => `${this.pick(nullable).name} ${this.pick(['===', '!=='])} null`);
        }
        break;
      }
      default:
        break;
    }
    return this.pick(options)();
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
    const u = this.pick([BIGINT, NUMBER]);
    const numeric = vars.filter((v) => !v.owned && same(v.ty, u));
    const left = numeric.length > 0 ? this.pick(numeric).name : this.expr(u, vars, depth);
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
          reads.push(`${v.name}.${field}`);
        }
      }
    }
    return reads;
  }

  private object(name: string, vars: ReadonlyArray<Var>, depth: number): string {
    const s = this.structs.find((x) => x.name === name);
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
      if (roll < 0.3) {
        const t = this.pick([BIGINT, NUMBER, BOOLEAN, STRING, ...(this.structs.length > 0 ? [{ k: 'struct', name: this.pick(this.structs).name } as Ty] : [])]);
        const name = this.fresh('v');
        const mutable = this.chance(0.6);
        const annotate = t.k === 'struct' || this.chance(0.2);
        lines.push(`${mutable ? 'let' : 'const'} ${name}${annotate ? `: ${show(t)}` : ''} = ${this.expr(t, vars, 2)};`);
        vars.push({ name, ty: t, mutable, owned: false });
      } else if (roll < 0.5 && lets.length > 0) {
        const v = this.pick(lets);
        const op = v.ty.k === 'bigint' || v.ty.k === 'number' ? this.pick(['=', '+=', '-=', '*=']) : '=';
        lines.push(`${v.name} ${op} ${this.expr(v.ty, vars, 2)};`);
      } else if (roll < 0.65 && depth > 0 && lets.length > 0) {
        const v = this.pick(lets);
        lines.push(`if (${this.test(vars, 2)}) {`, `  ${v.name} = ${this.expr(v.ty, vars, 1)};`, '}');
      } else if (roll < 0.8 && depth > 0) {
        const arrays = vars.filter((v) => v.ty.k === 'array' && !v.owned);
        const target = lets.length > 0 ? this.pick(lets) : undefined;
        if (arrays.length > 0 && target !== undefined) {
          const xs = this.pick(arrays);
          if (xs.ty.k === 'array') {
            const element = this.fresh('e');
            const inner = [...vars, { name: element, ty: xs.ty.of, mutable: false, owned: false }];
            lines.push(`for (const ${element} of ${xs.name}) {`, `  ${target.name} = ${this.expr(target.ty, inner, 1)};`, '}');
          }
        }
      } else if (roll < 0.88 && depth > 0) {
        // An array that the function owns, with a push; a later loop can read it.
        const t = this.pick([BIGINT, NUMBER]);
        const name = this.fresh('o');
        const start = this.chance(0.5) ? this.expr(t, vars, 0) : '';
        lines.push(`const ${name}: Array<${show(t)}> = [${start}];`, `${name}.push(${this.expr(t, vars, 1)});`);
        vars.push({ name, ty: { k: 'array', of: t }, mutable: false, owned: false });
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

  /** The interfaces and the functions of the program, in order. */
  signatures(): Signatures {
    return { structs: this.structs, functions: this.functions };
  }

  program(): string {
    const out: Array<string> = [];
    const structCount = Math.floor(this.next() * 3);
    for (let i = 0; i < structCount; i++) {
      const name = `S${i}`;
      const fields: Array<[string, Ty]> = [];
      const n = 1 + Math.floor(this.next() * 3);
      for (let j = 0; j < n; j++) {
        fields.push([`f${j}`, this.pick([BIGINT, NUMBER, BOOLEAN, STRING, { k: 'nullable', of: NUMBER } as Ty])]);
      }
      out.push(`interface ${name} {`, ...fields.map(([f, t]) => `  readonly ${f}: ${show(t)};`), '}');
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
      // Sometimes nullable, so that a call can return `null`.
      const ret = this.chance(0.3) && this.structs.length > 0
        ? ({ k: 'struct', name: this.pick(this.structs).name } as Ty)
        : this.chance(0.15) ? ({ k: 'nullable', of: this.pick([BIGINT, NUMBER]) } as Ty) : this.scalar();
      const signature = vars.map((v) => `${v.name}: ${show(v.ty)}`).join(', ');
      const nullable = vars.filter((v) => v.ty.k === 'nullable');
      const lines: Array<string> = [];
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
