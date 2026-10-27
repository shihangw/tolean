/**
 * The reference for the Lean TypeScript parser: `tsc`'s syntax tree, printed
 * in the S-expression form of `tolean/TypeScript/Syntax/Print.lean`.
 *
 * It maps only the node kinds that the Lean parser reads, and refuses the
 * rest, with the same rules the Lean parser applies after parsing (such as
 * "no `return` outside a function"). So for every file:
 *
 * - if both accept it, the two trees must be equal, spans included;
 * - if this refuses it, the Lean parser must refuse it too.
 *
 * Columns count Unicode code points, as in the Lean parser.
 */
import ts from 'typescript';

export type Sexp = {
  head: string;
  span?: string;
  atoms: Array<string>;
  children: Array<Sexp>;
};

export type TscResult =
  | { kind: 'tree'; sexp: string }
  | { kind: 'refused'; reason: string };

class Refused extends Error {}

/** The same rendering as `Sexp.render` in `tolean/Sexp.lean`. */
export function render(s: Sexp, indent = 0): string {
  const first = [s.head, ...(s.span === undefined ? [] : [s.span]), ...s.atoms].join(' ');
  const rest = s.children
    .map((child) => `\n${' '.repeat(indent + 2)}${render(child, indent + 2)}`)
    .join('');
  return `(${first}${rest})`;
}

const REFUSED_NAMES = new Set([
  'implements',
  'interface',
  'let',
  'package',
  'private',
  'protected',
  'public',
  'static',
  'yield',
  'await',
  'eval',
  'arguments',
]);

const TYPE_OPERATOR_WORDS = new Set(['keyof', 'unique', 'readonly', 'infer', 'asserts', 'is']);

const KEYWORD_TYPES = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.AnyKeyword, 'any'],
  [ts.SyntaxKind.UnknownKeyword, 'unknown'],
  [ts.SyntaxKind.NumberKeyword, 'number'],
  [ts.SyntaxKind.BigIntKeyword, 'bigint'],
  [ts.SyntaxKind.BooleanKeyword, 'boolean'],
  [ts.SyntaxKind.StringKeyword, 'string'],
  [ts.SyntaxKind.SymbolKeyword, 'symbol'],
  [ts.SyntaxKind.ObjectKeyword, 'object'],
  [ts.SyntaxKind.NeverKeyword, 'never'],
  [ts.SyntaxKind.UndefinedKeyword, 'undefined'],
  [ts.SyntaxKind.VoidKeyword, 'void'],
]);

const BINARY_OPS = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.QuestionQuestionToken, '??'],
  [ts.SyntaxKind.BarBarToken, '||'],
  [ts.SyntaxKind.AmpersandAmpersandToken, '&&'],
  [ts.SyntaxKind.BarToken, '|'],
  [ts.SyntaxKind.CaretToken, '^'],
  [ts.SyntaxKind.AmpersandToken, '&'],
  [ts.SyntaxKind.EqualsEqualsToken, '=='],
  [ts.SyntaxKind.ExclamationEqualsToken, '!='],
  [ts.SyntaxKind.EqualsEqualsEqualsToken, '==='],
  [ts.SyntaxKind.ExclamationEqualsEqualsToken, '!=='],
  [ts.SyntaxKind.LessThanToken, '<'],
  [ts.SyntaxKind.GreaterThanToken, '>'],
  [ts.SyntaxKind.LessThanEqualsToken, '<='],
  [ts.SyntaxKind.GreaterThanEqualsToken, '>='],
  [ts.SyntaxKind.InstanceOfKeyword, 'instanceof'],
  [ts.SyntaxKind.InKeyword, 'in'],
  [ts.SyntaxKind.LessThanLessThanToken, '<<'],
  [ts.SyntaxKind.GreaterThanGreaterThanToken, '>>'],
  [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken, '>>>'],
  [ts.SyntaxKind.PlusToken, '+'],
  [ts.SyntaxKind.MinusToken, '-'],
  [ts.SyntaxKind.AsteriskToken, '*'],
  [ts.SyntaxKind.SlashToken, '/'],
  [ts.SyntaxKind.PercentToken, '%'],
  [ts.SyntaxKind.AsteriskAsteriskToken, '**'],
]);

const ASSIGN_OPS = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.EqualsToken, '='],
  [ts.SyntaxKind.PlusEqualsToken, '+='],
  [ts.SyntaxKind.MinusEqualsToken, '-='],
  [ts.SyntaxKind.AsteriskEqualsToken, '*='],
  [ts.SyntaxKind.SlashEqualsToken, '/='],
  [ts.SyntaxKind.PercentEqualsToken, '%='],
  [ts.SyntaxKind.AsteriskAsteriskEqualsToken, '**='],
  [ts.SyntaxKind.LessThanLessThanEqualsToken, '<<='],
  [ts.SyntaxKind.GreaterThanGreaterThanEqualsToken, '>>='],
  [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken, '>>>='],
  [ts.SyntaxKind.AmpersandEqualsToken, '&='],
  [ts.SyntaxKind.BarEqualsToken, '|='],
  [ts.SyntaxKind.CaretEqualsToken, '^='],
  [ts.SyntaxKind.AmpersandAmpersandEqualsToken, '&&='],
  [ts.SyntaxKind.BarBarEqualsToken, '||='],
  [ts.SyntaxKind.QuestionQuestionEqualsToken, '??='],
]);

const PREFIX_OPS = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.ExclamationToken, '!'],
  [ts.SyntaxKind.MinusToken, '-'],
  [ts.SyntaxKind.PlusToken, '+'],
  [ts.SyntaxKind.TildeToken, '~'],
]);

const UPDATE_OPS = new Map<ts.SyntaxKind, string>([
  [ts.SyntaxKind.PlusPlusToken, '++'],
  [ts.SyntaxKind.MinusMinusToken, '--'],
]);

function refuse(node: ts.Node, reason: string): never {
  throw new Refused(`${ts.SyntaxKind[node.kind]}: ${reason}`);
}

function lookup<K, V>(map: Map<K, V>, key: K, node: ts.Node): V {
  const value = map.get(key);
  if (value === undefined) {
    refuse(node, `unsupported ${ts.SyntaxKind[key as ts.SyntaxKind]}`);
  }
  return value;
}

class Printer {
  private readonly sf: ts.SourceFile;
  private readonly text: string;
  private inFunction = false;
  private loopDepth = 0;

  constructor(sf: ts.SourceFile) {
    this.sf = sf;
    this.text = sf.text;
  }

  private pos(offset: number): string {
    const { line } = this.sf.getLineAndCharacterOfPosition(offset);
    const lineStart = this.sf.getLineStarts()[line] ?? 0;
    const col = [...this.text.slice(lineStart, offset)].length + 1;
    return `${line + 1}:${col}`;
  }

  private span(node: ts.Node): string {
    return `${this.pos(node.getStart(this.sf))}-${this.pos(node.getEnd())}`;
  }

  private node(
    head: string,
    node: ts.Node,
    atoms: Array<string>,
    children: Array<Sexp>,
  ): Sexp {
    return { head, span: this.span(node), atoms, children };
  }

  private raw(node: ts.Node): string {
    return node.getText(this.sf);
  }

  private name(node: ts.Node): string {
    if (!ts.isIdentifier(node)) {
      refuse(node, 'expected a name');
    }
    const name = node.text;
    if (REFUSED_NAMES.has(name)) {
      refuse(node, `'${name}' is not supported as a name`);
    }
    return name;
  }

  /** Allow only the modifiers in `allowed`. */
  private modifiers(node: ts.Node, allowed: Array<ts.SyntaxKind>): Set<ts.SyntaxKind> {
    const found = new Set<ts.SyntaxKind>();
    for (const m of ts.canHaveModifiers(node) ? (ts.getModifiers(node) ?? []) : []) {
      if (!allowed.includes(m.kind)) {
        refuse(m, 'unsupported modifier');
      }
      found.add(m.kind);
    }
    if (ts.canHaveDecorators(node) && (ts.getDecorators(node)?.length ?? 0) > 0) {
      refuse(node, 'decorators');
    }
    return found;
  }

  module(): Sexp {
    return {
      head: 'module',
      atoms: [],
      children: this.sf.statements.map((s) => this.topLevel(s)),
    };
  }

  private topLevel(s: ts.Statement): Sexp {
    if (ts.isImportDeclaration(s)) {
      return this.importDecl(s);
    }
    if (ts.isFunctionDeclaration(s)) {
      return this.functionDecl(s);
    }
    if (ts.isInterfaceDeclaration(s)) {
      const exported = this.modifiers(s, [ts.SyntaxKind.ExportKeyword]).size > 0;
      if (s.typeParameters !== undefined) {
        refuse(s, 'generic interface');
      }
      if (s.heritageClauses !== undefined) {
        refuse(s, 'extends');
      }
      return this.node(
        'interface',
        s,
        [this.name(s.name), ...(exported ? ['export'] : [])],
        s.members.map((m) => this.field(m)),
      );
    }
    if (ts.isTypeAliasDeclaration(s)) {
      const exported = this.modifiers(s, [ts.SyntaxKind.ExportKeyword]).size > 0;
      if (s.typeParameters !== undefined) {
        refuse(s, 'generic type alias');
      }
      return this.node(
        'type',
        s,
        [this.name(s.name), ...(exported ? ['export'] : [])],
        [this.type(s.type)],
      );
    }
    if (ts.isVariableStatement(s)) {
      const exported = this.modifiers(s, [ts.SyntaxKind.ExportKeyword]).size > 0;
      return this.variable(s, exported);
    }
    return this.statement(s);
  }

  // `import { a, type B } from "./x.ts"` and `import type { B } from "./x.ts"`.
  private importDecl(s: ts.ImportDeclaration): Sexp {
    const clause = s.importClause;
    if (clause === undefined || clause.name !== undefined || s.attributes !== undefined) {
      refuse(s, 'import form');
    }
    const bindings = clause.namedBindings;
    if (bindings === undefined || !ts.isNamedImports(bindings)) {
      refuse(s, 'import form');
    }
    if (clause.phaseModifier === ts.SyntaxKind.DeferKeyword) {
      refuse(s, 'import defer');
    }
    const clauseType = clause.phaseModifier === ts.SyntaxKind.TypeKeyword;
    const names = bindings.elements.map((el) => {
      if (el.propertyName !== undefined) {
        refuse(el, 'import alias');
      }
      const typeOnly = clauseType || el.isTypeOnly;
      return this.node('name', el.name, [this.name(el.name), ...(typeOnly ? ['type'] : [])], []);
    });
    const source = (s.moduleSpecifier as ts.StringLiteral).text;
    return this.node('import', s, [JSON.stringify(source)], names);
  }

  private functionDecl(s: ts.FunctionDeclaration): Sexp {
    const exported = this.modifiers(s, [ts.SyntaxKind.ExportKeyword]).size > 0;
    if (s.asteriskToken !== undefined) {
      refuse(s, 'generator');
    }
    if (s.typeParameters !== undefined) {
      refuse(s, 'generic function');
    }
    if (s.name === undefined || s.body === undefined) {
      refuse(s, 'function without a name or a body');
    }
    const params = s.parameters.map((p) => {
      this.modifiers(p, []);
      if (p.dotDotDotToken !== undefined || p.questionToken !== undefined) {
        refuse(p, 'rest or optional parameter');
      }
      if (p.initializer !== undefined) {
        refuse(p, 'default value');
      }
      return this.node(
        'param',
        p,
        [this.name(p.name)],
        p.type === undefined ? [] : [this.type(p.type)],
      );
    });
    const returnType = s.type === undefined ? [] : [this.type(s.type)];
    this.inFunction = true;
    const body = this.statement(s.body);
    this.inFunction = false;
    return this.node(
      'function',
      s,
      [this.name(s.name), ...(exported ? ['export'] : [])],
      [...params, ...returnType, body],
    );
  }

  private field(m: ts.TypeElement): Sexp {
    if (!ts.isPropertySignature(m)) {
      refuse(m, 'not a property signature');
    }
    const readonly = this.modifiers(m, [ts.SyntaxKind.ReadonlyKeyword]).size > 0;
    if (!ts.isIdentifier(m.name)) {
      refuse(m.name, 'field name');
    }
    if (m.type === undefined) {
      refuse(m, 'field without a type');
    }
    if ((m as { initializer?: ts.Expression }).initializer !== undefined) {
      refuse(m, 'field initializer');
    }
    return this.node(
      'field',
      m,
      [
        m.name.text,
        ...(readonly ? ['readonly'] : []),
        ...(m.questionToken === undefined ? [] : ['optional']),
      ],
      [this.type(m.type)],
    );
  }

  private variable(s: ts.VariableStatement, exported: boolean): Sexp {
    const list = s.declarationList;
    const kind = this.declarationKind(list);
    const [decl, ...more] = list.declarations;
    if (decl === undefined || more.length > 0) {
      refuse(s, 'not exactly one declarator');
    }
    if (decl.exclamationToken !== undefined) {
      refuse(decl, 'definite assignment');
    }
    if (kind === 'const' && decl.initializer === undefined) {
      refuse(decl, 'const without a value');
    }
    return this.node(
      kind,
      s,
      [this.name(decl.name), ...(exported ? ['export'] : [])],
      [
        ...(decl.type === undefined ? [] : [this.type(decl.type)]),
        ...(decl.initializer === undefined ? [] : [this.expr(decl.initializer)]),
      ],
    );
  }

  private declarationKind(list: ts.VariableDeclarationList): 'const' | 'let' {
    const flags = list.flags & ts.NodeFlags.BlockScoped;
    if (flags === ts.NodeFlags.Const) {
      return 'const';
    }
    if (flags === ts.NodeFlags.Let) {
      return 'let';
    }
    refuse(list, 'not const or let');
  }

  /** The body of `if`, `else`, `for` or `while`. */
  private branch(s: ts.Statement): Sexp {
    if (ts.isVariableStatement(s)) {
      refuse(s, 'declaration without a block');
    }
    return this.statement(s);
  }

  private loopBody(s: ts.Statement): Sexp {
    this.loopDepth += 1;
    const body = this.branch(s);
    this.loopDepth -= 1;
    return body;
  }

  private statement(s: ts.Statement): Sexp {
    if (ts.isVariableStatement(s)) {
      this.modifiers(s, []);
      return this.variable(s, false);
    }
    if (ts.isExpressionStatement(s)) {
      return this.node('expr', s, [], [this.expr(s.expression)]);
    }
    if (ts.isReturnStatement(s)) {
      if (!this.inFunction) {
        refuse(s, 'return outside a function');
      }
      return this.node('return', s, [], s.expression === undefined ? [] : [this.expr(s.expression)]);
    }
    if (ts.isIfStatement(s)) {
      const children = [this.expr(s.expression), this.branch(s.thenStatement)];
      if (s.elseStatement !== undefined) {
        children.push(this.branch(s.elseStatement));
      }
      return this.node('if', s, [], children);
    }
    if (ts.isForOfStatement(s)) {
      if (s.awaitModifier !== undefined) {
        refuse(s, 'for await');
      }
      const init = s.initializer;
      if (!ts.isVariableDeclarationList(init)) {
        refuse(init, 'for-of without a declaration');
      }
      const kind = this.declarationKind(init);
      const [decl, ...more] = init.declarations;
      if (decl === undefined || more.length > 0 || decl.type !== undefined) {
        refuse(init, 'for-of declaration');
      }
      return this.node(
        'for-of',
        s,
        [kind, this.name(decl.name)],
        [this.expr(s.expression), this.loopBody(s.statement)],
      );
    }
    if (ts.isWhileStatement(s)) {
      return this.node('while', s, [], [this.expr(s.expression), this.loopBody(s.statement)]);
    }
    if (ts.isBlock(s)) {
      return this.node('block', s, [], s.statements.map((st) => this.statement(st)));
    }
    if (ts.isBreakStatement(s) || ts.isContinueStatement(s)) {
      if (s.label !== undefined) {
        refuse(s, 'label');
      }
      if (this.loopDepth === 0) {
        refuse(s, 'outside a loop');
      }
      return this.node(ts.isBreakStatement(s) ? 'break' : 'continue', s, [], []);
    }
    if (ts.isEmptyStatement(s)) {
      return this.node('empty', s, [], []);
    }
    refuse(s, 'unsupported statement');
  }

  private expr(e: ts.Expression): Sexp {
    if (ts.isIdentifier(e)) {
      return this.node('ident', e, [this.name(e)], []);
    }
    if (ts.isNumericLiteral(e)) {
      return this.node('number', e, [this.raw(e)], []);
    }
    if (ts.isBigIntLiteral(e)) {
      return this.node('bigint', e, [this.raw(e)], []);
    }
    if (ts.isStringLiteral(e)) {
      return this.node('string', e, [JSON.stringify(e.text)], []);
    }
    switch (e.kind) {
      case ts.SyntaxKind.TrueKeyword:
        return this.node('true', e, [], []);
      case ts.SyntaxKind.FalseKeyword:
        return this.node('false', e, [], []);
      case ts.SyntaxKind.NullKeyword:
        return this.node('null', e, [], []);
      default:
        break;
    }
    if (ts.isArrayLiteralExpression(e)) {
      return this.node(
        'array',
        e,
        [],
        e.elements.map((el) => {
          if (ts.isOmittedExpression(el) || ts.isSpreadElement(el)) {
            refuse(el, 'hole or spread');
          }
          return this.expr(el);
        }),
      );
    }
    if (ts.isObjectLiteralExpression(e)) {
      return this.node(
        'object',
        e,
        [],
        e.properties.map((p) => this.property(p)),
      );
    }
    if (ts.isParenthesizedExpression(e)) {
      return this.node('paren', e, [], [this.expr(e.expression)]);
    }
    if (ts.isPropertyAccessExpression(e)) {
      if (e.questionDotToken !== undefined || !ts.isIdentifier(e.name)) {
        refuse(e, 'optional chain or private name');
      }
      return this.node('member', e, [e.name.text], [this.expr(e.expression)]);
    }
    if (ts.isElementAccessExpression(e)) {
      if (e.questionDotToken !== undefined) {
        refuse(e, 'optional chain');
      }
      return this.node('index', e, [], [this.expr(e.expression), this.expr(e.argumentExpression)]);
    }
    if (ts.isCallExpression(e)) {
      if (e.questionDotToken !== undefined || e.typeArguments !== undefined) {
        refuse(e, 'optional call or type arguments');
      }
      return this.node('call', e, [], [
        this.expr(e.expression),
        ...e.arguments.map((a) => {
          if (ts.isSpreadElement(a)) {
            refuse(a, 'spread argument');
          }
          return this.expr(a);
        }),
      ]);
    }
    if (ts.isPrefixUnaryExpression(e)) {
      const update = UPDATE_OPS.get(e.operator);
      if (update !== undefined) {
        this.target(e.operand);
        return this.node('prefix', e, [update], [this.expr(e.operand)]);
      }
      return this.node('unary', e, [lookup(PREFIX_OPS, e.operator, e)], [this.expr(e.operand)]);
    }
    if (ts.isPostfixUnaryExpression(e)) {
      this.target(e.operand);
      return this.node('postfix', e, [lookup(UPDATE_OPS, e.operator, e)], [this.expr(e.operand)]);
    }
    if (ts.isTypeOfExpression(e)) {
      return this.node('unary', e, ['typeof'], [this.expr(e.expression)]);
    }
    if (ts.isVoidExpression(e)) {
      return this.node('unary', e, ['void'], [this.expr(e.expression)]);
    }
    if (ts.isBinaryExpression(e)) {
      const kind = e.operatorToken.kind;
      const assign = ASSIGN_OPS.get(kind);
      if (assign !== undefined) {
        this.target(e.left);
        return this.node('assign', e, [assign], [this.expr(e.left), this.expr(e.right)]);
      }
      const op = lookup(BINARY_OPS, kind, e.operatorToken);
      this.checkMixing(e, op);
      if (op === '**' && this.isUnaryOperation(e.left)) {
        refuse(e, 'unary operand of **');
      }
      return this.node('binary', e, [op], [this.expr(e.left), this.expr(e.right)]);
    }
    if (ts.isConditionalExpression(e)) {
      return this.node('cond', e, [], [
        this.expr(e.condition),
        this.expr(e.whenTrue),
        this.expr(e.whenFalse),
      ]);
    }
    refuse(e, 'unsupported expression');
  }

  /** A unary operation, which cannot be the base of `**`. An update such as
   * `--x` can. */
  private isUnaryOperation(e: ts.Expression): boolean {
    return (
      (ts.isPrefixUnaryExpression(e) && !UPDATE_OPS.has(e.operator)) ||
      ts.isTypeOfExpression(e) ||
      ts.isVoidExpression(e)
    );
  }

  /** `??` cannot be mixed with `&&` or `||` without parentheses. */
  private checkMixing(e: ts.BinaryExpression, op: string): void {
    const opOf = (x: ts.Expression): string | undefined =>
      ts.isBinaryExpression(x) ? BINARY_OPS.get(x.operatorToken.kind) : undefined;
    const sides = [opOf(e.left), opOf(e.right)];
    const logical = (o: string | undefined): boolean => o === '&&' || o === '||';
    if (op === '??' && sides.some(logical)) {
      refuse(e, '?? mixed with && or ||');
    }
    if (logical(op) && sides.includes('??')) {
      refuse(e, '?? mixed with && or ||');
    }
  }

  /** Only a name, a property or an element can be assigned. */
  private target(e: ts.Expression): void {
    let inner = e;
    while (ts.isParenthesizedExpression(inner)) {
      inner = inner.expression;
    }
    if (
      !ts.isIdentifier(inner) &&
      !ts.isPropertyAccessExpression(inner) &&
      !ts.isElementAccessExpression(inner)
    ) {
      refuse(e, 'assignment target');
    }
  }

  private property(p: ts.ObjectLiteralElementLike): Sexp {
    if (ts.isShorthandPropertyAssignment(p)) {
      if (p.objectAssignmentInitializer !== undefined) {
        refuse(p, 'shorthand initializer');
      }
      return this.node('shorthand', p, [this.name(p.name)], []);
    }
    if (!ts.isPropertyAssignment(p)) {
      refuse(p, 'unsupported property');
    }
    const key = p.name;
    let atom: string;
    if (ts.isIdentifier(key)) {
      atom = key.text;
    } else if (ts.isStringLiteral(key)) {
      atom = JSON.stringify(key.text);
    } else if (ts.isNumericLiteral(key)) {
      atom = this.raw(key);
    } else {
      refuse(key, 'unsupported key');
    }
    return this.node('property', p, [atom], [this.expr(p.initializer)]);
  }

  private type(t: ts.TypeNode): Sexp {
    const keyword = KEYWORD_TYPES.get(t.kind);
    if (keyword !== undefined) {
      return this.node('type-keyword', t, [keyword], []);
    }
    if (ts.isLiteralTypeNode(t)) {
      const lit = t.literal;
      switch (lit.kind) {
        case ts.SyntaxKind.NullKeyword:
          return this.node('type-null', t, [], []);
        case ts.SyntaxKind.TrueKeyword:
          return this.node('type-literal', t, ['true'], []);
        case ts.SyntaxKind.FalseKeyword:
          return this.node('type-literal', t, ['false'], []);
        case ts.SyntaxKind.StringLiteral:
          return this.node('type-literal', t, [JSON.stringify((lit as ts.StringLiteral).text)], []);
        case ts.SyntaxKind.NumericLiteral:
        case ts.SyntaxKind.BigIntLiteral:
          return this.node('type-literal', t, [this.raw(lit)], []);
        default:
          refuse(t, 'unsupported literal type');
      }
    }
    if (ts.isTypeReferenceNode(t)) {
      if (!ts.isIdentifier(t.typeName)) {
        refuse(t, 'qualified name');
      }
      const name = t.typeName.text;
      if (TYPE_OPERATOR_WORDS.has(name)) {
        refuse(t, `'${name}' as a type name`);
      }
      return this.node(
        'type-ref',
        t,
        [this.name(t.typeName)],
        (t.typeArguments ?? []).map((a) => this.type(a)),
      );
    }
    if (ts.isArrayTypeNode(t)) {
      return this.node('type-array', t, [], [this.type(t.elementType)]);
    }
    if (ts.isUnionTypeNode(t)) {
      return this.node('type-union', t, [], t.types.map((m) => this.type(m)));
    }
    if (ts.isParenthesizedTypeNode(t)) {
      return this.node('type-paren', t, [], [this.type(t.type)]);
    }
    refuse(t, 'unsupported type');
  }
}

/** Parse `text` with `tsc` and print its tree, or say why it is refused. */
export function tscAst(fileName: string, text: string): TscResult {
  const sf = ts.createSourceFile(fileName, text, ts.ScriptTarget.Latest, true, ts.ScriptKind.TS);
  const diagnostics = (sf as unknown as { parseDiagnostics: Array<ts.Diagnostic> })
    .parseDiagnostics;
  const first = diagnostics[0];
  if (first !== undefined) {
    return {
      kind: 'refused',
      reason: `tsc: ${ts.flattenDiagnosticMessageText(first.messageText, '\n')}`,
    };
  }
  try {
    return { kind: 'tree', sexp: render(new Printer(sf).module()) };
  } catch (error) {
    if (error instanceof Refused) {
      return { kind: 'refused', reason: error.message };
    }
    throw error;
  }
}
