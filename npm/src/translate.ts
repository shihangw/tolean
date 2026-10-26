/**
 * Translate one self-contained TypeScript file, written in a small pure
 * subset, to Lean 4 definitions that compute the same values.
 *
 * The translation is a shallow embedding: each function becomes a `def`, each
 * interface a `structure`, and local mutation becomes shadowed `let`s. A
 * `for…of` loop becomes `List.foldl` over the tuple of locals it changes. That
 * is sound only because the subset rules out aliasing: the only mutable
 * values are locals the function owns (`let` scalars and `const` arrays
 * initialised to `[]`), and nothing else can observe them.
 *
 * `number` is never Lean's `Float`: definitions become generic over an
 * abstract number type `N` (`tolean.TypeScript.JSNumber`), and `T | null` becomes
 * `Option T`, with TypeScript's null narrowing as a `match`.
 *
 * Anything outside the subset is rejected with a `TranslateError`, never
 * approximated. See README.md for the accepted subset.
 */
import { readFileSync } from 'node:fs';

import ts from 'typescript';

export class TranslateError extends Error {}

/** The tolean release, which generated files name. It must equal `version`
 * in `tolean/Version.lean`. */
const VERSION: string = (
  JSON.parse(readFileSync(new URL('../package.json', import.meta.url), 'utf8')) as {
    version: string;
  }
).version;

/**
 * The editions of ECMA-262 that a translation can target, as in
 * `tolean/TypeScript/Edition.lean`. The code runs as written (type stripping
 * keeps its syntax), so the target must have every feature it uses.
 */
export const EDITIONS = [
  'ES2015',
  'ES2016',
  'ES2017',
  'ES2018',
  'ES2019',
  'ES2020',
  'ES2021',
  'ES2022',
  'ES2023',
  'ES2024',
  'ES2025',
] as const;

export type Edition = (typeof EDITIONS)[number];

/** What Node 22 supports: the oldest Node release line still maintained. */
export const DEFAULT_TARGET: Edition = 'ES2024';

/** The JS features tolean relies on, the first edition that specifies each
 * as tolean reads it, and how messages name it. */
const FEATURES = {
  exponent: { since: 'ES2016', describe: "'**'" },
  bigint: { since: 'ES2020', describe: 'bigint' },
  bigintDivision: { since: 'ES2020', describe: "bigint '/' and '%'" },
  nullishCoalescing: { since: 'ES2020', describe: "'??'" },
  logicalAssignment: { since: 'ES2021', describe: "'&&=', '||=' and '??='" },
  numericSeparators: { since: 'ES2021', describe: 'numeric separators' },
} as const satisfies Record<string, { since: Edition; describe: string }>;

type Feature = keyof typeof FEATURES;

export function parseEdition(name: string): Edition | null {
  return EDITIONS.find((e) => e.toLowerCase() === name.toLowerCase()) ?? null;
}

function supports(target: Edition, feature: Feature): boolean {
  return EDITIONS.indexOf(FEATURES[feature].since) <= EDITIONS.indexOf(target);
}

function requireFeature(context: Context, node: ts.Node, feature: Feature): void {
  if (!supports(context.target, feature)) {
    const { since, describe } = FEATURES[feature];
    throw reject(
      context,
      node,
      `the target ${context.target} does not have ${describe} (added in ${since})`,
    );
  }
}

/** Refuse syntax that the target does not have, anywhere in the file. */
function checkSyntax(context: Context, node: ts.Node): void {
  if (ts.isBigIntLiteral(node) || node.kind === ts.SyntaxKind.BigIntKeyword) {
    requireFeature(context, node, 'bigint');
  }
  if (
    (ts.isBigIntLiteral(node) || ts.isNumericLiteral(node)) &&
    node.getText(context.sourceFile).includes('_')
  ) {
    requireFeature(context, node, 'numericSeparators');
  }
  if (ts.isBinaryExpression(node)) {
    switch (node.operatorToken.kind) {
      case ts.SyntaxKind.AsteriskAsteriskToken:
      case ts.SyntaxKind.AsteriskAsteriskEqualsToken:
        requireFeature(context, node.operatorToken, 'exponent');
        break;
      case ts.SyntaxKind.QuestionQuestionToken:
        requireFeature(context, node.operatorToken, 'nullishCoalescing');
        break;
      case ts.SyntaxKind.AmpersandAmpersandEqualsToken:
      case ts.SyntaxKind.BarBarEqualsToken:
      case ts.SyntaxKind.QuestionQuestionEqualsToken:
        requireFeature(context, node.operatorToken, 'logicalAssignment');
        break;
      default:
        break;
    }
  }
  ts.forEachChild(node, (child) => checkSyntax(context, child));
}

type LeanType = string;

/** How a name in scope may be used. Only `let` and `array` locals are mutable. */
type Binding = 'param' | 'const' | 'let' | 'array';

type Env = ReadonlyMap<string, Binding>;

/** A translated expression; `prop` is true when it is a Lean `Prop`, not a `Bool`. */
interface Expr {
  code: string;
  prop: boolean;
}

/** What a statement list must end in: a `return`, or the tuple of changed locals. */
type Tail =
  | { kind: 'return' }
  | { kind: 'state'; names: ReadonlyArray<string> };

type Lines = ReadonlyArray<string>;

interface Context {
  /** The edition the code runs on. */
  target: Edition;
  checker: ts.TypeChecker;
  sourceFile: ts.SourceFile;
  /** Interface name → field name → Lean type. */
  structs: Map<string, Map<string, LeanType>>;
  /** Functions declared so far; a call may only name one of these. */
  functions: Set<string>;
  currentFunction: string;
  /**
   * True while translating a `return` value. An owned array may be read only
   * there: a later push would shadow the array in Lean but mutate it in JS,
   * so any earlier read (an alias, a captured field, a loop over it) could
   * see a stale value.
   */
  returning: boolean;
  /**
   * The file uses `number`. Then every structure and def is generic over an
   * abstract number type `N` (`tolean.TypeScript.JSNumber`), never Lean's `Float`,
   * which has no lemmas.
   */
  usesNumber: boolean;
  /**
   * Lean names the output uses that the source also declares. The output
   * writes them in full from the root, so a source name never hides them.
   */
  clashes: Set<string>;
  /** The number type parameter: `N`, or a fresh name when the source uses `N`. */
  numberVar: string;
}

/** The Lean names the output uses, with their full names from the root. */
const LEAN_NAMES = new Map<string, string>([
  ['decide', 'Decidable.decide'],
  ['List', 'List'],
  ['Option', 'Option'],
  ['some', 'Option.some'],
  ['none', 'Option.none'],
  ['Int', 'Int'],
  ['Bool', 'Bool'],
  ['String', 'String'],
  ['JSNumber', 'tolean.TypeScript.JSNumber'],
]);

/**
 * Write the Lean name `name` (or `name.rest`), from the root when the source
 * declares the same name.
 */
function leanName(context: Context, name: string): string {
  const [head = name, ...rest] = name.split('.');
  if (!context.clashes.has(head)) {
    return name;
  }
  return ['_root_.' + (LEAN_NAMES.get(head) ?? head), ...rest].join('.');
}

/** Every identifier token in the source, at any level. */
function identifiers(text: string): Set<string> {
  const scanner = ts.createScanner(ts.ScriptTarget.ES2022, true, ts.LanguageVariant.Standard, text);
  const names = new Set<string>();
  for (let kind = scanner.scan(); kind !== ts.SyntaxKind.EndOfFileToken; kind = scanner.scan()) {
    if (kind === ts.SyntaxKind.Identifier) {
      names.add(scanner.getTokenValue());
    }
  }
  return names;
}

const LEAN_RESERVED = new Set([
  '_root_',
  'abbrev',
  'at',
  'axiom',
  'by',
  'class',
  'def',
  'deriving',
  'do',
  'else',
  'end',
  'example',
  'extends',
  'for',
  'from',
  'fun',
  'have',
  'if',
  'import',
  'in',
  'inductive',
  'instance',
  'let',
  'match',
  'mut',
  'namespace',
  'open',
  'private',
  'protected',
  'return',
  'section',
  'show',
  'structure',
  'then',
  'theorem',
  'universe',
  'unless',
  'variable',
  'where',
  'with',
  'Type',
  'Prop',
  'Sort',
]);

/** `Number.<test>(x)` and its Lean form. */
const NUMBER_TESTS: Partial<Record<string, (js: string, tested: string) => string>> = {
  isSafeInteger: (js, tested) => `(${js}.toSafeInt ${tested}).isSome`,
  isNaN: (js, tested) => `(${js}.isNaN ${tested})`,
  isFinite: (js, tested) => `(${js}.isFinite ${tested})`,
};

/** Global number constants and their `JSNumber` names. `-Infinity` is `negInf`. */
const NUMBER_CONSTANTS: Partial<Record<string, string>> = {
  NaN: 'nan',
  Infinity: 'posInf',
};

const COMPILER_OPTIONS: ts.CompilerOptions = {
  strict: true,
  noEmit: true,
  target: ts.ScriptTarget.ES2022,
  lib: ['lib.es2022.d.ts'],
  types: [],
};

export function translateSource({
  fileName,
  text,
  namespace,
  target = DEFAULT_TARGET,
}: {
  fileName: string;
  text: string;
  namespace: string;
  /** The edition the code runs on. */
  target?: Edition;
}): string {
  const sourceFile = ts.createSourceFile(
    fileName,
    text,
    ts.ScriptTarget.ES2022,
    true,
  );
  const host = ts.createCompilerHost(COMPILER_OPTIONS);
  const readSourceFile = host.getSourceFile.bind(host);
  host.getSourceFile = (name, languageVersion, onError, shouldCreate) =>
    name === fileName
      ? sourceFile
      : readSourceFile(name, languageVersion, onError, shouldCreate);
  const program = ts.createProgram([fileName], COMPILER_OPTIONS, host);
  const diagnostics = ts.getPreEmitDiagnostics(program, sourceFile);
  if (diagnostics.length > 0) {
    throw new TranslateError(
      `${fileName} does not type-check:\n${ts.formatDiagnostics(diagnostics, host)}`,
    );
  }

  const context: Context = {
    target,
    checker: program.getTypeChecker(),
    sourceFile,
    structs: new Map(),
    functions: new Set(),
    currentFunction: '',
    returning: false,
    usesNumber: containsNumber(sourceFile),
    clashes: new Set(),
    numberVar: 'N',
  };
  const names = identifiers(text);
  context.clashes = new Set([...LEAN_NAMES.keys()].filter((name) => names.has(name)));
  for (let i = 1; names.has(context.numberVar); i++) {
    context.numberVar = `N${i}`;
  }
  checkSyntax(context, sourceFile);
  const sections = sourceFile.statements.map((statement) => {
    if (ts.isInterfaceDeclaration(statement)) {
      return translateInterface(context, statement);
    }
    if (ts.isFunctionDeclaration(statement)) {
      return translateFunction(context, statement);
    }
    throw reject(
      context,
      statement,
      'only interfaces and functions may appear at top level',
    );
  });

  return [
    `-- Generated by tolean ${VERSION} for ${target} from ${fileName}. Do not edit.`,
    ...(context.usesNumber
      ? ['import tolean.TypeScript.Spec.Number', '', 'open tolean.TypeScript']
      : []),
    `namespace ${namespace}`,
    '',
    sections.join('\n\n'),
    '',
    `end ${namespace}`,
    '',
  ].join('\n');
}

/**
 * The file uses the number model: a `number` type, a numeric literal, a number
 * constant (`NaN`, `Infinity`), or anything on `Number`. A file can use
 * `Number.isNaN(NaN)` with no `number` keyword, and it still needs `N`.
 */
function containsNumber(node: ts.Node): boolean {
  if (
    node.kind === ts.SyntaxKind.NumberKeyword ||
    ts.isNumericLiteral(node) ||
    (ts.isIdentifier(node) &&
      (node.text === 'Number' || NUMBER_CONSTANTS[node.text] != null))
  ) {
    return true;
  }

  return ts.forEachChild(node, containsNumber) === true;
}

/** `Name`, or `(Name N)` when the file is generic over the number type. */
function structType(context: Context, name: string): LeanType {
  return context.usesNumber ? `(${name} ${context.numberVar})` : name;
}

function reject(
  context: Context,
  node: ts.Node,
  reason: string,
): TranslateError {
  const { line, character } = context.sourceFile.getLineAndCharacterOfPosition(
    node.getStart(context.sourceFile),
  );
  return new TranslateError(
    `${context.sourceFile.fileName}:${line + 1}:${character + 1}: ${reason}: ${node
      .getText(context.sourceFile)
      .slice(0, 80)}`,
  );
}

function checkName(context: Context, node: ts.Node, name: string): string {
  if (LEAN_RESERVED.has(name)) {
    throw reject(context, node, `name '${name}' is reserved in Lean`);
  }

  return name;
}

function translateInterface(
  context: Context,
  node: ts.InterfaceDeclaration,
): string {
  if (node.typeParameters != null || node.heritageClauses != null) {
    throw reject(
      context,
      node,
      'generic or extending interfaces are not supported',
    );
  }
  const name = checkName(context, node.name, node.name.text);
  const fields = new Map<string, LeanType>();
  for (const member of node.members) {
    if (
      !ts.isPropertySignature(member) ||
      !ts.isIdentifier(member.name) ||
      member.type == null ||
      member.questionToken != null ||
      !member.modifiers?.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword)
    ) {
      throw reject(
        context,
        member,
        'interface fields must be readonly, required and typed',
      );
    }
    fields.set(
      checkName(context, member.name, member.name.text),
      translateType(context, member.type),
    );
  }
  context.structs.set(name, fields);

  return [
    `structure ${name}${context.usesNumber ? ` (${context.numberVar} : Type)` : ''} where`,
    ...[...fields].map(([field, type]) => `  ${field} : ${type}`),
  ].join('\n');
}

function translateType(context: Context, node: ts.TypeNode): LeanType {
  switch (node.kind) {
    case ts.SyntaxKind.BigIntKeyword:
      return leanName(context, 'Int');
    case ts.SyntaxKind.BooleanKeyword:
      return leanName(context, 'Bool');
    case ts.SyntaxKind.StringKeyword:
      return leanName(context, 'String');
    case ts.SyntaxKind.NumberKeyword:
      return context.numberVar;
    default:
      break;
  }
  if (ts.isUnionTypeNode(node)) {
    // `T | null`: exactly two members, one of them `null`.
    const values = node.types.filter(
      (member) =>
        !(
          ts.isLiteralTypeNode(member) &&
          member.literal.kind === ts.SyntaxKind.NullKeyword
        ),
    );
    const [value] = values;
    if (node.types.length === 2 && values.length === 1 && value != null) {
      return wrapped(leanName(context, 'Option'), translateType(context, value));
    }
  }
  if (ts.isArrayTypeNode(node)) {
    return listOf(context, translateType(context, node.elementType));
  }
  if (
    ts.isTypeOperatorNode(node) &&
    node.operator === ts.SyntaxKind.ReadonlyKeyword &&
    ts.isArrayTypeNode(node.type)
  ) {
    return listOf(context, translateType(context, node.type.elementType));
  }
  if (ts.isTypeReferenceNode(node) && ts.isIdentifier(node.typeName)) {
    const name = node.typeName.text;
    const [element] = node.typeArguments ?? [];
    if (
      (name === 'Array' || name === 'ReadonlyArray') &&
      element != null &&
      node.typeArguments?.length === 1
    ) {
      return listOf(context, translateType(context, element));
    }
    if (node.typeArguments == null && context.structs.has(name)) {
      return structType(context, name);
    }
  }

  throw reject(
    context,
    node,
    'unsupported type (use bigint, number, boolean, string, T | null, arrays, or an interface declared above)',
  );
}

function listOf(context: Context, element: LeanType): LeanType {
  return wrapped(leanName(context, 'List'), element);
}

function wrapped(constructor: string, argument: LeanType): LeanType {
  return `${constructor} ${argument.includes(' ') && !argument.startsWith('(') ? `(${argument})` : argument}`;
}

function translateFunction(
  context: Context,
  node: ts.FunctionDeclaration,
): string {
  if (
    node.name == null ||
    node.body == null ||
    node.type == null ||
    node.typeParameters != null ||
    node.asteriskToken != null ||
    node.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)
  ) {
    throw reject(
      context,
      node,
      'functions must be named, typed, non-generic and synchronous',
    );
  }
  const name = checkName(context, node.name, node.name.text);
  context.currentFunction = name;
  const env = new Map<string, Binding>();
  const params = node.parameters.map((param) => {
    if (
      !ts.isIdentifier(param.name) ||
      param.type == null ||
      param.initializer != null ||
      param.questionToken != null ||
      param.dotDotDotToken != null
    ) {
      throw reject(
        context,
        param,
        'parameters must be plain, typed identifiers',
      );
    }
    const paramName = checkName(context, param.name, param.name.text);
    env.set(paramName, 'param');
    return `(${paramName} : ${translateType(context, param.type)})`;
  });
  const returnType = translateType(context, node.type);
  const body = translateStatements(context, [...node.body.statements], env, {
    kind: 'return',
  });
  context.functions.add(name);

  return [
    `def ${name}${context.usesNumber ? ` {${context.numberVar} : Type} [${leanName(context, 'JSNumber')} ${context.numberVar}]` : ''} ${params.join(' ')} : ${returnType} :=`,
    ...indent(body),
  ].join('\n');
}

function indent(lines: Lines, by = '  '): Lines {
  return lines.map((line) => `${by}${line}`);
}

function tuple(names: ReadonlyArray<string>): string {
  return names.length === 1 ? (names[0] ?? '') : `(${names.join(', ')})`;
}

/** True when every path through `statements` ends in a `return`. */
function alwaysReturns(statements: ReadonlyArray<ts.Statement>): boolean {
  const last = statements.at(-1);
  if (last == null) {
    return false;
  }
  if (ts.isReturnStatement(last)) {
    return true;
  }
  if (ts.isIfStatement(last) && last.elseStatement != null) {
    return (
      alwaysReturns(blockStatements(last.thenStatement)) &&
      alwaysReturns(blockStatements(last.elseStatement))
    );
  }

  return false;
}

function blockStatements(node: ts.Statement): ReadonlyArray<ts.Statement> {
  return ts.isBlock(node) ? [...node.statements] : [node];
}

/** True when `node` contains a `return`, `break` or `continue`. */
function containsJump(node: ts.Node): boolean {
  if (
    ts.isReturnStatement(node) ||
    ts.isBreakStatement(node) ||
    ts.isContinueStatement(node)
  ) {
    return true;
  }

  return ts.forEachChild(node, containsJump) === true;
}

/** Locals of `env` that `statements` assign or push to. */
function changedNames(
  statements: ReadonlyArray<ts.Statement>,
  env: Env,
): ReadonlyArray<string> {
  const names = new Set<string>();
  const visit = (node: ts.Node): void => {
    if (
      ts.isBinaryExpression(node) &&
      isAssignment(node.operatorToken.kind) &&
      ts.isIdentifier(node.left)
    ) {
      names.add(node.left.text);
    }
    if (
      (ts.isPostfixUnaryExpression(node) || ts.isPrefixUnaryExpression(node)) &&
      ts.isIdentifier(node.operand) &&
      (node.operator === ts.SyntaxKind.PlusPlusToken ||
        node.operator === ts.SyntaxKind.MinusMinusToken)
    ) {
      names.add(node.operand.text);
    }
    const pushTarget = pushTargetOf(node);
    if (pushTarget != null) {
      names.add(pushTarget);
    }
    ts.forEachChild(node, visit);
  };
  statements.forEach(visit);

  return [...env.keys()].filter((name) => names.has(name));
}

function isAssignment(kind: ts.SyntaxKind): boolean {
  return (
    kind === ts.SyntaxKind.EqualsToken ||
    kind === ts.SyntaxKind.PlusEqualsToken ||
    kind === ts.SyntaxKind.MinusEqualsToken ||
    kind === ts.SyntaxKind.AsteriskEqualsToken
  );
}

function pushTargetOf(node: ts.Node): string | null {
  if (
    ts.isCallExpression(node) &&
    ts.isPropertyAccessExpression(node.expression) &&
    node.expression.name.text === 'push' &&
    ts.isIdentifier(node.expression.expression)
  ) {
    return node.expression.expression.text;
  }

  return null;
}

function declare(
  context: Context,
  env: Env,
  node: ts.Node,
  name: string,
  binding: Binding,
): Env {
  if (env.has(name)) {
    throw reject(context, node, `'${name}' shadows a name already in scope`);
  }
  checkName(context, node, name);

  return new Map([...env, [name, binding]]);
}

function translateStatements(
  context: Context,
  statements: ReadonlyArray<ts.Statement>,
  env: Env,
  tail: Tail,
): Lines {
  const [statement, ...rest] = statements;
  if (statement == null) {
    if (tail.kind === 'return') {
      throw new TranslateError(
        `${context.sourceFile.fileName}: '${context.currentFunction}' can end without a return`,
      );
    }
    return [tuple(tail.names)];
  }

  if (ts.isReturnStatement(statement)) {
    if (
      tail.kind !== 'return' ||
      rest.length > 0 ||
      statement.expression == null
    ) {
      throw reject(
        context,
        statement,
        'return must be the last statement of a function and carry a value',
      );
    }
    context.returning = true;
    const returned = value(context, 
      translateExpression(context, statement.expression, env),
    );
    context.returning = false;
    return [returned];
  }

  if (ts.isVariableStatement(statement)) {
    return translateVariable(context, statement, rest, env, tail);
  }

  if (ts.isExpressionStatement(statement)) {
    const [name, update] = translateUpdate(context, statement.expression, env);
    return [
      `let ${name} := ${update}`,
      ...translateStatements(context, rest, env, tail),
    ];
  }

  if (ts.isIfStatement(statement)) {
    return translateIf(context, statement, rest, env, tail);
  }

  if (ts.isForOfStatement(statement)) {
    return translateForOf(context, statement, rest, env, tail);
  }

  throw reject(context, statement, 'unsupported statement');
}

function translateVariable(
  context: Context,
  statement: ts.VariableStatement,
  rest: ReadonlyArray<ts.Statement>,
  env: Env,
  tail: Tail,
): Lines {
  const list = statement.declarationList;
  const isConst = (list.flags & ts.NodeFlags.Const) !== 0;
  const isLet = (list.flags & ts.NodeFlags.Let) !== 0;
  const [declaration] = list.declarations;
  if (
    (!isConst && !isLet) ||
    list.declarations.length !== 1 ||
    declaration == null ||
    !ts.isIdentifier(declaration.name) ||
    declaration.initializer == null
  ) {
    throw reject(
      context,
      statement,
      'declare one const or let identifier with an initializer',
    );
  }
  const name = declaration.name.text;
  const initializer = declaration.initializer;

  if (ts.isArrayLiteralExpression(initializer)) {
    if (
      !isConst ||
      initializer.elements.length > 0 ||
      declaration.type == null
    ) {
      throw reject(
        context,
        statement,
        "an owned array must be 'const x: Array<T> = []'",
      );
    }
    const type = translateType(context, declaration.type);
    return [
      `let ${name} : ${type} := []`,
      ...translateStatements(
        context,
        rest,
        declare(context, env, declaration, name, 'array'),
        tail,
      ),
    ];
  }

  const expression = value(context, translateExpression(context, initializer, env));
  return [
    `let ${name} := ${expression}`,
    ...translateStatements(
      context,
      rest,
      declare(context, env, declaration, name, isLet ? 'let' : 'const'),
      tail,
    ),
  ];
}

/** One mutation statement as `[local, its new value]`. */
function translateUpdate(
  context: Context,
  expression: ts.Expression,
  env: Env,
): [string, string] {
  const pushTarget = pushTargetOf(expression);
  if (pushTarget != null && ts.isCallExpression(expression)) {
    const [element] = expression.arguments;
    if (
      env.get(pushTarget) !== 'array' ||
      expression.arguments.length !== 1 ||
      element == null ||
      ts.isSpreadElement(element)
    ) {
      throw reject(
        context,
        expression,
        'push is allowed only onto an owned array, one element at a time',
      );
    }
    return [
      pushTarget,
      `${pushTarget} ++ [${value(context, translateExpression(context, element, env))}]`,
    ];
  }

  if (
    ts.isBinaryExpression(expression) &&
    isAssignment(expression.operatorToken.kind) &&
    ts.isIdentifier(expression.left)
  ) {
    const name = expression.left.text;
    if (env.get(name) !== 'let') {
      throw reject(
        context,
        expression,
        `only a local declared with let may be assigned`,
      );
    }
    const right = value(context, translateExpression(context, expression.right, env));
    // On `number` the operation goes through the abstract number model.
    const combine = (
      bigintOperator: string,
      numberOperation: string,
    ): string =>
      isNumber(context, expression.left)
        ? `(${leanName(context, 'JSNumber')}.${numberOperation} ${name} ${argument(right)})`
        : `${name} ${bigintOperator} ${right}`;
    switch (expression.operatorToken.kind) {
      case ts.SyntaxKind.EqualsToken:
        return [name, right];
      case ts.SyntaxKind.PlusEqualsToken:
        return [name, combine('+', 'add')];
      case ts.SyntaxKind.MinusEqualsToken:
        return [name, combine('-', 'sub')];
      case ts.SyntaxKind.AsteriskEqualsToken:
        return [name, combine('*', 'mul')];
      default:
        break;
    }
  }

  throw reject(
    context,
    expression,
    'an expression statement must assign a let local or push to an owned array',
  );
}

function translateIf(
  context: Context,
  statement: ts.IfStatement,
  rest: ReadonlyArray<ts.Statement>,
  env: Env,
  tail: Tail,
): Lines {
  const thenStatements = blockStatements(statement.thenStatement);
  const elseStatements =
    statement.elseStatement == null
      ? []
      : blockStatements(statement.elseStatement);
  // `if (x === null)` / `if (x !== null)`: TypeScript narrows `x` in the
  // non-null branch, so Lean matches on `x` and rebinds it to the value.
  const test = nullTestOf(context, statement.expression, env);
  const branch = (
    whenTrue: ReadonlyArray<string>,
    whenFalse: ReadonlyArray<string>,
  ): Lines => {
    if (test == null) {
      const condition = translateExpression(
        context,
        statement.expression,
        env,
      ).code;
      return [
        `if ${condition} then`,
        ...indent(whenTrue),
        'else',
        ...indent(whenFalse),
      ];
    }
    const [name, isNullTest] = test;
    return [
      `match ${name} with`,
      `| ${leanName(context, 'none')} =>`,
      ...indent(isNullTest ? whenTrue : whenFalse),
      `| ${leanName(context, 'some')} ${name} =>`,
      ...indent(isNullTest ? whenFalse : whenTrue),
    ];
  };

  if (tail.kind === 'return' && alwaysReturns(thenStatements)) {
    if (statement.elseStatement != null && rest.length > 0) {
      throw reject(
        context,
        statement,
        'code after an if whose branches both return is unreachable',
      );
    }
    return branch(
      translateStatements(context, thenStatements, env, tail),
      translateStatements(context, [...elseStatements, ...rest], env, tail),
    );
  }

  if ([...thenStatements, ...elseStatements].some(containsJump)) {
    throw reject(
      context,
      statement,
      'a branch that does not always return may not return, break or continue',
    );
  }
  const names = changedNames([...thenStatements, ...elseStatements], env);
  if (names.length === 0) {
    throw reject(
      context,
      statement,
      'an if without a return must change a local',
    );
  }
  if (test != null && names.includes(test[0])) {
    throw reject(
      context,
      statement,
      'a local tested against null may not be assigned in that if',
    );
  }
  const state: Tail = { kind: 'state', names };
  return [
    `let ${tuple(names)} :=`,
    ...indent(
      branch(
        translateStatements(context, thenStatements, env, state),
        translateStatements(context, elseStatements, env, state),
      ),
    ),
    ...translateStatements(context, rest, env, tail),
  ];
}

function translateForOf(
  context: Context,
  statement: ts.ForOfStatement,
  rest: ReadonlyArray<ts.Statement>,
  env: Env,
  tail: Tail,
): Lines {
  const initializer = statement.initializer;
  const [declaration] = ts.isVariableDeclarationList(initializer)
    ? initializer.declarations
    : [];
  if (
    statement.awaitModifier != null ||
    !ts.isVariableDeclarationList(initializer) ||
    (initializer.flags & ts.NodeFlags.Const) === 0 ||
    declaration == null ||
    !ts.isIdentifier(declaration.name)
  ) {
    throw reject(context, statement, "a loop must be 'for (const x of xs)'");
  }
  const body = blockStatements(statement.statement);
  if (body.some(containsJump)) {
    throw reject(
      context,
      statement,
      'a loop body may not return, break or continue',
    );
  }
  const names = changedNames(body, env);
  if (names.length === 0) {
    throw reject(context, statement, 'a loop must change a local');
  }
  const element = declaration.name.text;
  const items = translateExpression(context, statement.expression, env).code;
  const bodyEnv = declare(context, env, declaration, element, 'const');
  const bodyLines = translateStatements(context, body, bodyEnv, {
    kind: 'state',
    names,
  });
  const lastLine = bodyLines.at(-1) ?? '';

  return [
    `let ${tuple(names)} :=`,
    `  ${leanName(context, 'List.foldl')}`,
    `    (fun ${tuple(names)} ${element} =>`,
    ...indent([...bodyLines.slice(0, -1), `${lastLine})`], '      '),
    `    ${tuple(names)} ${items}`,
    ...translateStatements(context, rest, env, tail),
  ];
}

/** An expression in value position: a `Prop` becomes a `Bool` via `decide`. */
function value(context: Context, expression: Expr): string {
  return expression.prop
    ? `${leanName(context, 'decide')} (${expression.code})`
    : expression.code;
}

/**
 * The type is of this kind. A union counts only when every member does: `c ? 0 : 1`
 * has the type `0 | 1`, whose own flags say union, not number.
 */
function hasTypeKind(
  context: Context,
  node: ts.Expression,
  kind: ts.TypeFlags,
): boolean {
  const type = context.checker.getTypeAtLocation(node);
  return type.isUnion()
    ? type.types.every((member) => (member.flags & kind) !== 0)
    : (type.flags & kind) !== 0;
}

function isBigInt(context: Context, node: ts.Expression): boolean {
  return hasTypeKind(context, node, ts.TypeFlags.BigIntLike);
}

function isObject(context: Context, node: ts.Expression): boolean {
  return (
    (context.checker.getTypeAtLocation(node).flags & ts.TypeFlags.Object) !== 0
  );
}

function structName(
  context: Context,
  type: ts.Type | undefined,
): string | null {
  const name = type?.getSymbol()?.getName();
  return name != null && context.structs.has(name) ? name : null;
}

function translateExpression(
  context: Context,
  node: ts.Expression,
  env: Env,
): Expr {
  const bool = (code: string): Expr => ({ code, prop: false });
  const prop = (code: string): Expr => ({ code, prop: true });

  if (ts.isParenthesizedExpression(node)) {
    return translateExpression(context, node.expression, env);
  }
  if (ts.isBigIntLiteral(node)) {
    // In decimal, and typed, so Lean never defaults a numeral to `Nat`, where
    // `0 - 1 = 0`.
    return bool(`(${BigInt(node.text.slice(0, -1)).toString()} : ${leanName(context, 'Int')})`);
  }
  if (ts.isNumericLiteral(node)) {
    const literal = Number(node.text);
    if (!Number.isSafeInteger(literal)) {
      throw reject(context, node, 'a number literal must be a safe integer');
    }
    return bool(`(${leanName(context, 'JSNumber')}.ofSafeInt (N := ${context.numberVar}) (${literal} : ${leanName(context, 'Int')}))`);
  }
  if (node.kind === ts.SyntaxKind.NullKeyword) {
    return bool(leanName(context, 'none'));
  }
  if (node.kind === ts.SyntaxKind.TrueKeyword) {
    return bool('true');
  }
  if (node.kind === ts.SyntaxKind.FalseKeyword) {
    return bool('false');
  }
  if (ts.isStringLiteral(node)) {
    return bool(JSON.stringify(node.text));
  }
  if (ts.isIdentifier(node)) {
    const constant = env.has(node.text)
      ? undefined
      : NUMBER_CONSTANTS[node.text];
    if (constant != null) {
      return bool(`(${leanName(context, 'JSNumber')}.${constant} (N := ${context.numberVar}))`);
    }
    if (!env.has(node.text)) {
      throw reject(
        context,
        node,
        'only parameters and locals may be referenced',
      );
    }
    if (env.get(node.text) === 'array' && !context.returning) {
      throw reject(
        context,
        node,
        'an owned array may be read only in the return value',
      );
    }
    return bool(node.text);
  }
  if (ts.isPropertyAccessExpression(node)) {
    const struct = structName(
      context,
      context.checker.getTypeAtLocation(node.expression),
    );
    if (struct == null || !context.structs.get(struct)?.has(node.name.text)) {
      throw reject(
        context,
        node,
        'only fields of interfaces declared in this file may be read',
      );
    }
    const object = translateExpression(context, node.expression, env).code;
    return bool(
      `${ts.isIdentifier(node.expression) ? object : `(${object})`}.${node.name.text}`,
    );
  }
  if (ts.isPrefixUnaryExpression(node)) {
    if (
      node.operator === ts.SyntaxKind.MinusToken &&
      ts.isIdentifier(node.operand) &&
      node.operand.text === 'Infinity' &&
      !env.has('Infinity')
    ) {
      return bool(`(${leanName(context, 'JSNumber')}.negInf (N := ${context.numberVar}))`);
    }
    const operand = translateExpression(context, node.operand, env);
    switch (node.operator) {
      case ts.SyntaxKind.ExclamationToken:
        return operand.prop
          ? prop(`¬(${operand.code})`)
          : bool(`!(${operand.code})`);
      case ts.SyntaxKind.MinusToken:
        if (isBigInt(context, node.operand)) {
          return bool(`(-${value(context, operand)})`);
        }
        if (isNumber(context, node.operand)) {
          return bool(`(${leanName(context, 'JSNumber')}.neg ${argument(value(context, operand))})`);
        }
        break;
      default:
        break;
    }
    throw reject(context, node, 'unsupported unary operator');
  }
  if (ts.isBinaryExpression(node)) {
    return translateBinary(context, node, env);
  }
  if (ts.isConditionalExpression(node)) {
    const condition = translateExpression(context, node.condition, env).code;
    const whenTrue = value(context, translateExpression(context, node.whenTrue, env));
    const whenFalse = value(context, translateExpression(context, node.whenFalse, env));
    return bool(`(if ${condition} then ${whenTrue} else ${whenFalse})`);
  }
  if (ts.isCallExpression(node)) {
    const [onlyArgument] = node.arguments;
    const numberTest =
      ts.isPropertyAccessExpression(node.expression) &&
      ts.isIdentifier(node.expression.expression) &&
      node.expression.expression.text === 'Number' &&
      !env.has('Number')
        ? node.expression.name.text
        : undefined;
    const translateTest =
      numberTest == null ? undefined : NUMBER_TESTS[numberTest];
    if (
      translateTest != null &&
      node.arguments.length === 1 &&
      onlyArgument != null &&
      !ts.isSpreadElement(onlyArgument)
    ) {
      // TypeScript lets these take any value; the model has them on numbers only.
      if (!isNumber(context, onlyArgument)) {
        throw reject(
          context,
          onlyArgument,
          `Number.${numberTest} needs a number operand (narrow a nullable value first)`,
        );
      }
      return bool(
        translateTest(
          leanName(context, 'JSNumber'),
          argument(value(context, translateExpression(context, onlyArgument, env))),
        ),
      );
    }
    if (
      ts.isIdentifier(node.expression) &&
      (node.expression.text === 'isNaN' ||
        node.expression.text === 'isFinite') &&
      !context.functions.has(node.expression.text)
    ) {
      throw reject(
        context,
        node,
        `the global ${node.expression.text} converts its argument to a number; use Number.${node.expression.text}`,
      );
    }
    if (
      !ts.isIdentifier(node.expression) ||
      !context.functions.has(node.expression.text) ||
      node.typeArguments != null
    ) {
      throw reject(
        context,
        node,
        'calls may name only functions declared earlier in this file (no recursion)',
      );
    }
    const args = node.arguments.map((arg) => {
      if (ts.isSpreadElement(arg)) {
        throw reject(context, arg, 'spread arguments are not supported');
      }
      const translated = value(context, translateExpression(context, arg, env));
      return translated.includes(' ') ? `(${translated})` : translated;
    });
    // Every def is generic over `N` when the file uses numbers. Name it, so
    // that a callee whose signature does not mention `N` still elaborates.
    const generic = context.usesNumber ? [`(N := ${context.numberVar})`] : [];
    return bool(`(${[node.expression.text, ...generic, ...args].join(' ')})`);
  }
  if (ts.isObjectLiteralExpression(node)) {
    return bool(translateObject(context, node, env));
  }

  throw reject(context, node, 'unsupported expression');
}

function isNumber(context: Context, node: ts.Expression): boolean {
  return hasTypeKind(context, node, ts.TypeFlags.NumberLike);
}

/**
 * What TypeScript knows about `null` at this point, after its narrowing: the
 * value is `null`, may be `null` (a Lean `Option`), or cannot be `null` (in
 * Lean it is already the value inside). Not just any union is nullable:
 * `boolean` is `true | false`.
 */
function nullnessOf(
  context: Context,
  node: ts.Expression,
): 'null' | 'nullable' | 'notNull' {
  const type = context.checker.getTypeAtLocation(node);
  if ((type.flags & ts.TypeFlags.Null) !== 0) {
    return 'null';
  }
  return type.isUnion() &&
    type.types.some((member) => (member.flags & ts.TypeFlags.Null) !== 0)
    ? 'nullable'
    : 'notNull';
}

function isNullable(context: Context, node: ts.Expression): boolean {
  return nullnessOf(context, node) === 'nullable';
}

function isNullLiteral(node: ts.Expression): boolean {
  return node.kind === ts.SyntaxKind.NullKeyword;
}

/** In `e === null` or `null === e`, the `e`; otherwise null. */
function comparedWithNull(node: ts.BinaryExpression): ts.Expression | null {
  if (isNullLiteral(node.right)) {
    return node.left;
  }
  if (isNullLiteral(node.left)) {
    return node.right;
  }

  return null;
}

/** An argument position: parenthesised unless it is one token. */
function argument(code: string): string {
  return code.includes(' ') ? `(${code})` : code;
}

/**
 * `x === null` or `x !== null` on a name in scope that may be `null` here, as
 * `[x, isNullTest]`. A name TypeScript has already narrowed is not an
 * `Option` in Lean any more, so it gets no `match`.
 */
function nullTestOf(
  context: Context,
  node: ts.Expression,
  env: Env,
): [string, boolean] | null {
  let inner = node;
  while (ts.isParenthesizedExpression(inner)) {
    inner = inner.expression;
  }
  if (!ts.isBinaryExpression(inner)) {
    return null;
  }
  const operator = inner.operatorToken.kind;
  if (
    operator !== ts.SyntaxKind.EqualsEqualsEqualsToken &&
    operator !== ts.SyntaxKind.ExclamationEqualsEqualsToken
  ) {
    return null;
  }
  const other = comparedWithNull(inner);
  if (
    other == null ||
    !ts.isIdentifier(other) ||
    !env.has(other.text) ||
    !isNullable(context, other)
  ) {
    return null;
  }

  return [other.text, operator === ts.SyntaxKind.EqualsEqualsEqualsToken];
}

function translateBinary(
  context: Context,
  node: ts.BinaryExpression,
  env: Env,
): Expr {
  const operator = node.operatorToken.kind;

  // `x === null` / `x !== null`: a test on a Lean `Option`.
  if (
    (operator === ts.SyntaxKind.EqualsEqualsEqualsToken ||
      operator === ts.SyntaxKind.ExclamationEqualsEqualsToken) &&
    (isNullLiteral(node.left) || isNullLiteral(node.right))
  ) {
    const other = isNullLiteral(node.left) ? node.right : node.left;
    if (isNullLiteral(other)) {
      throw reject(context, node, 'compare null with a value, not with null');
    }
    const isEquality = operator === ts.SyntaxKind.EqualsEqualsEqualsToken;
    // Translate the operand even when the answer is fixed: translating is what
    // refuses anything outside the subset, such as an assignment inside it.
    // What the subset accepts has no side effects, so its value can be dropped.
    const tested = argument(translateExpression(context, other, env).code);
    const nullness = nullnessOf(context, other);
    if (nullness !== 'nullable') {
      // Already narrowed: the answer is fixed, as it is in JS.
      return {
        code: String(isEquality === (nullness === 'null')),
        prop: false,
      };
    }
    return {
      code: `${tested}.${isEquality ? 'isNone' : 'isSome'}`,
      prop: false,
    };
  }

  // `x === null || e` and `x !== null && e`: TypeScript narrows `x` in `e`, so
  // Lean matches on `x` and rebinds it to the value inside.
  const test = nullTestOf(context, node.left, env);
  if (
    test != null &&
    ((operator === ts.SyntaxKind.BarBarToken && test[1]) ||
      (operator === ts.SyntaxKind.AmpersandAmpersandToken && !test[1]))
  ) {
    const [name] = test;
    const whenSome = value(context, translateExpression(context, node.right, env));
    const whenNone = operator === ts.SyntaxKind.BarBarToken ? 'true' : 'false';
    return {
      code: `(match ${name} with | ${leanName(context, 'none')} => ${whenNone} | ${leanName(context, 'some')} ${name} => ${whenSome})`,
      prop: false,
    };
  }

  const left = translateExpression(context, node.left, env);
  const right = translateExpression(context, node.right, env);
  const bothBigInt =
    isBigInt(context, node.left) && isBigInt(context, node.right);
  const bothNumber =
    isNumber(context, node.left) && isNumber(context, node.right);
  const call = (name: string, a: Expr, b: Expr): Expr => ({
    code: `(${leanName(context, 'JSNumber')}.${name} ${argument(value(context, a))} ${argument(value(context, b))})`,
    prop: false,
  });
  const arithmetic = (
    bigintOperator: string,
    numberOperation: string,
  ): Expr => {
    if (bothNumber) {
      return call(numberOperation, left, right);
    }
    if (!bothBigInt) {
      throw reject(
        context,
        node,
        'arithmetic needs two bigints or two numbers',
      );
    }
    return {
      code: `(${value(context, left)} ${bigintOperator} ${value(context, right)})`,
      prop: false,
    };
  };
  // `a > b` is `b < a`, and `a >= b` is `b <= a`.
  const compare = (
    bigintOperator: string,
    numberOperation: string,
    swap: boolean,
  ): Expr => {
    if (bothNumber) {
      return swap
        ? call(numberOperation, right, left)
        : call(numberOperation, left, right);
    }
    if (!bothBigInt) {
      throw reject(context, node, 'ordering needs two bigints or two numbers');
    }
    return {
      code: `${value(context, left)} ${bigintOperator} ${value(context, right)}`,
      prop: true,
    };
  };
  const equal = (negated: boolean): Expr => {
    if (bothNumber) {
      const eq = call('eq', left, right);
      return negated ? { code: `!${eq.code}`, prop: false } : eq;
    }
    if (
      isObject(context, node.left) ||
      isObject(context, node.right) ||
      isNullable(context, node.left) ||
      isNullable(context, node.right)
    ) {
      throw reject(
        context,
        node,
        '=== here would compare objects or nullable values; only primitives and null tests are supported',
      );
    }
    return {
      code: `${value(context, left)} ${negated ? '≠' : '='} ${value(context, right)}`,
      prop: true,
    };
  };
  // bigint `/` truncates toward zero and `%` takes the sign of the dividend:
  // Lean's `Int.tdiv` and `Int.tmod`. JS throws on a zero divisor, where Lean
  // gives a value, so the divisor must be a nonzero literal.
  const divide = (operation: string): Expr => {
    if (!bothBigInt || !isNonzeroBigIntLiteral(node.right)) {
      throw reject(
        context,
        node,
        "'/' and '%' need two bigints and a nonzero bigint literal divisor (JS throws on 0n)",
      );
    }
    requireFeature(context, node, 'bigintDivision');
    return {
      code: `(${leanName(context, 'Int')}.${operation} ${argument(value(context, left))} ${argument(value(context, right))})`,
      prop: false,
    };
  };
  const logical = (propOperator: string, boolOperator: string): Expr =>
    left.prop && right.prop
      ? { code: `(${left.code}) ${propOperator} (${right.code})`, prop: true }
      : {
          code: `(${value(context, left)} ${boolOperator} ${value(context, right)})`,
          prop: false,
        };

  switch (operator) {
    case ts.SyntaxKind.PlusToken:
      return arithmetic('+', 'add');
    case ts.SyntaxKind.MinusToken:
      return arithmetic('-', 'sub');
    case ts.SyntaxKind.AsteriskToken:
      return arithmetic('*', 'mul');
    case ts.SyntaxKind.SlashToken:
      return divide('tdiv');
    case ts.SyntaxKind.PercentToken:
      return divide('tmod');
    case ts.SyntaxKind.LessThanToken:
      return compare('<', 'lt', false);
    case ts.SyntaxKind.LessThanEqualsToken:
      return compare('≤', 'le', false);
    case ts.SyntaxKind.GreaterThanToken:
      return compare('>', 'lt', true);
    case ts.SyntaxKind.GreaterThanEqualsToken:
      return compare('≥', 'le', true);
    case ts.SyntaxKind.EqualsEqualsEqualsToken:
      return equal(false);
    case ts.SyntaxKind.ExclamationEqualsEqualsToken:
      return equal(true);
    case ts.SyntaxKind.AmpersandAmpersandToken:
      return logical('∧', '&&');
    case ts.SyntaxKind.BarBarToken:
      return logical('∨', '||');
    default:
      throw reject(context, node, 'unsupported binary operator');
  }
}

/** A bigint literal other than `0n`, such as `2n` or `-(3n)`. */
function isNonzeroBigIntLiteral(node: ts.Expression): boolean {
  let inner = node;
  while (ts.isParenthesizedExpression(inner)) {
    inner = inner.expression;
  }
  if (
    ts.isPrefixUnaryExpression(inner) &&
    inner.operator === ts.SyntaxKind.MinusToken
  ) {
    return isNonzeroBigIntLiteral(inner.operand);
  }
  return ts.isBigIntLiteral(inner) && BigInt(inner.text.slice(0, -1)) !== 0n;
}

function translateObject(
  context: Context,
  node: ts.ObjectLiteralExpression,
  env: Env,
): string {
  const struct = structName(context, context.checker.getContextualType(node));
  const fields = struct == null ? undefined : context.structs.get(struct);
  if (struct == null || fields == null) {
    throw reject(
      context,
      node,
      'an object literal must build an interface declared in this file',
    );
  }
  const assignments = node.properties.map((property) => {
    if (ts.isShorthandPropertyAssignment(property)) {
      return `${property.name.text} := ${value(context, translateExpression(context, property.name, env))}`;
    }
    if (ts.isPropertyAssignment(property) && ts.isIdentifier(property.name)) {
      return `${property.name.text} := ${value(context, translateExpression(context, property.initializer, env))}`;
    }
    throw reject(
      context,
      property,
      'object literal fields must be plain name: value pairs',
    );
  });

  return `({ ${assignments.join(', ')} } : ${structType(context, struct)})`;
}
