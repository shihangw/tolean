import Lean
import tolean.TypeScript.Proof.Module
import tolean.TypeScript.Syntax.Equality
import tolean.TypeScript.Syntax.Source
import tolean.TypeScript.Spec.Lemmas.Number
import tolean.TypeScript.Spec.Coverage.LexicalGrammar
import tolean.TypeScript.Spec.Coverage.Expressions
import tolean.TypeScript.Spec.Coverage.Statements
import tolean.TypeScript.Spec.Coverage.Modules
import tolean.TypeScript.Spec.Coverage.Extras

/-!
Every theorem about the TypeScript subset, under the section of ECMA-262 that
it is about. The index shows how well the theorems cover the spec.

`sections` lists, in the order of the spec, each section that the
interpreter follows. `program_sound` covers all of them at once, because it
holds for every program that the translator accepts. So `everySection` lists
it first, with the inductions that prove it. Under each section are the
theorems about that section's construct. A section with no theorems is
covered only by `everySection`. `numberLaws` lists the laws of the number
model from §6.1.6.1. The proofs assume them, and tests check them against
Node, so they are trusted, not proved.

`extras` lists the theorems that are about no section: the translator's
machinery, the rules that come from Lean, and the parser.

The build checks the index. Each name must be a theorem that exists, so a
rename breaks the build. The check at the end of this file fails when a
theorem of the TypeScript modules is in no list, so a new theorem must find
its place here.

The files in `Spec/Coverage/` hold checks that the interpreter and the
translator follow a rule that one of them once broke. They hold `#guard`
checks too, for rules about concrete strings.

Every heading about the spec, in this file and in `Spec/Coverage/`, has one
form, so that a script can read them all and compare them with each other
and with the spec:

    §<number> <title> {#<anchor>}

A chapter has this form as the title of its file in `Spec/Coverage/`, and as
a `--` comment in `sections`. A section has it as a heading of level 3, with
the number, the title and the anchor of its entry in `sections`. A heading of
the extras is `### Extras: <heading>`, with the heading of its group in
`extras`, and the file of the extras has the title `Extras`.

Each section has its anchor in the spec, its number in ES2024, the default
target, and its title. The anchor, such as `sec-unary-minus-operator`, stays
the same from one edition to the next, but numbers move: four of the 38
sections here have another number in ES2025 or ES2026. So when the default
target moves to a newer edition, each number can be read again from that
edition's table of contents by its anchor.
-/
namespace tolean.TypeScript.Coverage

open Lean

/-- A section of ECMA-262, and the theorems about its construct. `id` is the
section's anchor in the spec, such as `sec-unary-minus-operator`, so the
section is at `https://tc39.es/ecma262/2024/#<id>`. The anchor stays the same
from one edition to the next, but `number` can change. -/
structure Section where
  id : String
  number : String
  title : String
  theorems : List Name

/-- A heading of the index that names no section, and the theorems under it. -/
structure Group where
  heading : String
  theorems : List Name

/-- The theorems that cover every section of the subset at once. -/
def everySection : Group :=
  ⟨"Every section of the subset", [``Proof.program_sound, ``Proof.translate_sound,
    ``Proof.programTranslation_rel, ``Proof.expr_sound, ``Proof.stmts_sound]⟩

/-- The sections of ECMA-262 that the interpreter follows, in the order of
the spec, with the theorems about each. -/
def sections : List Section := [
  -- §6 ECMAScript Data Types and Values {#sec-ecmascript-data-types-and-values}
  ⟨"sec-ecmascript-language-types-number-type", "6.1.6.1", "The Number Type",
    [``eq_refl_of_safe, ``le_refl_of_safe, ``lt_irrefl_of_safe, ``eq_self_eq_not_isNaN,
    ``eq_posInf_posInf, ``eq_negInf_negInf, ``isNaN_eq_false_of_safe]⟩,
  ⟨"sec-ecmascript-language-types-bigint-type", "6.1.6.2", "The BigInt Type", []⟩,
  -- §7 Abstract Operations {#sec-abstract-operations}
  ⟨"sec-toboolean", "7.1.2", "ToBoolean", []⟩,
  ⟨"sec-isstrictlyequal", "7.2.15", "IsStrictlyEqual", []⟩,
  -- §9 Executable Code and Execution Contexts {#sec-executable-code-and-execution-contexts}
  ⟨"sec-declarative-environment-records", "9.1.1.1", "Declarative Environment Records",
    [``Eval.Env.set_cons, ``Eval.Env.lookup_cons, ``Eval.Env.length_set, ``Eval.Env.set_set,
    ``Eval.Env.set_of_lookup, ``Eval.Env.lookup_set_same, ``Eval.Env.lookup_set_ne,
    ``Eval.Env.set_comm, ``Eval.Env.set_merge1, ``Eval.Env.set_merge2, ``Eval.Env.set_merge3,
    ``Eval.Env.set_merge4, ``Eval.Env.set_merge5, ``Eval.Env.set_merge6, ``Eval.Env.set_merge7,
    ``Eval.Env.set_merge8]⟩,
  -- §10 Ordinary and Exotic Objects Behaviours {#sec-ordinary-and-exotic-objects-behaviours}
  ⟨"sec-ecmascript-function-objects-call-thisargument-argumentslist", "10.2.1", "[[Call]]",
    [``Proof.scoped_params]⟩,
  -- §12 ECMAScript Language: Lexical Grammar {#sec-ecmascript-language-lexical-grammar}
  ⟨"sec-literals-numeric-literals", "12.9.3", "Numeric Literals", []⟩,
  -- §13 ECMAScript Language: Expressions {#sec-ecmascript-language-expressions}
  ⟨"sec-identifiers", "13.1", "Identifiers",
    [``Proof.Scoped.none, ``Proof.Scoped.some]⟩,
  ⟨"sec-primary-expression-literals", "13.2.3", "Literals", []⟩,
  ⟨"sec-array-initializer", "13.2.4", "Array Initializer",
    [``Proof.mapM_sim]⟩,
  ⟨"sec-runtime-semantics-propertydefinitionevaluation", "13.2.5.5",
    "Runtime Semantics: PropertyDefinitionEvaluation",
    [``Proof.fold_sim, ``shorthand_reads_global]⟩,
  ⟨"sec-grouping-operator", "13.2.9", "The Grouping Operator",
    [``Proof.eval_stripParens]⟩,
  ⟨"sec-property-accessors", "13.3.2", "Property Accessors", []⟩,
  ⟨"sec-function-calls", "13.3.6", "Function Calls",
    [``Proof.eval_call, ``Proof.out_call, ``Proof.zip_sim, ``Proof.calls_agree]⟩,
  ⟨"sec-unary-minus-operator", "13.5.5", "Unary - Operator",
    [``Proof.operator_sound, ``Proof.eval_neg, ``Proof.out_neg, ``Proof.out_numberNeg,
    ``Proof.isInfinity_eq_true, ``neg_local_infinity]⟩,
  ⟨"sec-logical-not-operator", "13.5.7", "Logical NOT Operator",
    [``Proof.operator_sound, ``Proof.out_not, ``Proof.out_propNot]⟩,
  ⟨"sec-multiplicative-operators", "13.7", "Multiplicative Operators",
    [``Proof.operator_sound, ``Proof.eval_binary, ``Proof.out_intOp, ``Proof.out_numberOp,
    ``Proof.out_division, ``Proof.nonzero_literal]⟩,
  ⟨"sec-additive-operators", "13.8", "Additive Operators",
    [``Proof.operator_sound, ``Proof.eval_binary, ``Proof.out_intOp, ``Proof.out_numberOp]⟩,
  ⟨"sec-relational-operators", "13.10", "Relational Operators",
    [``Proof.operator_sound, ``Proof.eval_binary, ``Proof.out_order, ``Proof.out_numberOp]⟩,
  ⟨"sec-equality-operators", "13.11", "Equality Operators",
    [``Proof.operator_sound, ``Proof.eval_binary, ``Proof.out_eq, ``Proof.out_ne,
    ``Proof.out_numberOp, ``Proof.out_numberNe, ``Proof.out_isNone, ``Proof.out_isSome,
    ``Proof.isNull_eq_true, ``Proof.nullTestOf_eval]⟩,
  ⟨"sec-binary-logical-operators", "13.13", "Binary Logical Operators",
    [``Proof.operator_sound, ``Proof.out_and, ``Proof.out_or]⟩,
  ⟨"sec-conditional-operator", "13.14", "Conditional Operator",
    [``Proof.out_ite]⟩,
  ⟨"sec-assignment-operators", "13.15", "Assignment Operators",
    [``Proof.update_sound, ``Proof.out_update, ``Proof.agree_set]⟩,
  -- §14 ECMAScript Language: Statements and Declarations {#sec-ecmascript-language-statements-and-declarations}
  ⟨"sec-block", "14.2", "Block",
    [``Proof.exec_single, ``Proof.blockStatements_eq, ``Proof.execStmt_block, ``Proof.block_ret,
    ``Proof.block_normal, ``Proof.stmtsChanges_append, ``Proof.stmtsChanges_block,
    ``Proof.mem_changedNames, ``Proof.lookup_append_fresh, ``Proof.bindState_lookup,
    ``Proof.scoped_frame, ``Proof.Frame.refl, ``Proof.Frame.length, ``Proof.Frame.mono,
    ``Proof.Frame.trans, ``Proof.Frame.lookup, ``Proof.Frame.isSome, ``Proof.Frame.set,
    ``Proof.Frame.append, ``Proof.Frame.mem, ``Proof.Frame.split]⟩,
  ⟨"sec-let-and-const-declarations", "14.3.1", "Let and Const Declarations",
    [``Proof.decl_sim, ``Proof.declare_ok, ``Proof.has_add, ``declare_not_callable]⟩,
  ⟨"sec-if-statement", "14.6", "The if Statement",
    [``Proof.execStmt_if, ``Proof.if_ret, ``Proof.if_normal, ``Proof.if_ret_sim,
    ``Proof.if_state_sim, ``Proof.branch_ite, ``Proof.branch_null]⟩,
  ⟨"sec-for-in-and-for-of-statements", "14.7.5",
    "The for-in, for-of, and for-await-of Statements",
    [``Proof.loop_sim, ``Eval.execLoop_foldl]⟩,
  ⟨"sec-return-statement", "14.10", "The return Statement", []⟩,
  -- §15 ECMAScript Language: Functions and Classes {#sec-ecmascript-language-functions-and-classes}
  ⟨"sec-function-definitions", "15.2", "Function Definitions",
    [``Proof.translateFunction_ok, ``Proof.params_fold]⟩,
  -- §16 ECMAScript Language: Scripts and Modules {#sec-ecmascript-language-scripts-and-modules}
  ⟨"sec-source-text-module-record-initialize-environment", "16.2.1.6.4", "InitializeEnvironment",
    [``Proof.module_resolves, ``Proof.declareTopLevel_ok, ``Proof.translateDecl_ok,
    ``Proof.decls_ok, ``declareTopLevel_not_global]⟩,
  ⟨"sec-HostLoadImportedModule", "16.2.1.8", "HostLoadImportedModule",
    [``resolvePath_url, ``resolvePath_relative, ``resolvePath_last]⟩,
  ⟨"sec-imports", "16.2.2", "Imports",
    [``Proof.translateImport_ok]⟩,
  ⟨"sec-exports", "16.2.3", "Exports", []⟩,
  -- §19 The Global Object {#sec-global-object}
  ⟨"sec-value-properties-of-the-global-object-infinity", "19.1.2", "Infinity", []⟩,
  ⟨"sec-value-properties-of-the-global-object-nan", "19.1.3", "NaN", []⟩,
  -- §21 Numbers and Dates {#sec-numbers-and-dates}
  ⟨"sec-properties-of-the-number-constructor", "21.1.2", "Properties of the Number Constructor",
    [``Proof.out_numberTest]⟩,
  -- §23 Indexed Collections {#sec-indexed-collections}
  ⟨"sec-array.prototype.push", "23.1.3.23", "Array.prototype.push",
    [``Proof.out_push]⟩,
  ⟨"sec-createarrayiterator", "23.1.5.1", "CreateArrayIterator", []⟩]

/-- The laws of the number model, from §6.1.6.1 The Number Type. The proofs
assume them instead of proving them, and `tests/typescript/jsNumberLaws.test.ts`
checks each one against the doubles of every maintained Node release line. -/
def numberLaws : List Name := [``SafeIntLaws.add,
    ``SafeIntLaws.sub, ``SafeIntLaws.mul, ``SafeIntLaws.neg, ``SafeIntLaws.eq, ``SafeIntLaws.lt,
    ``SafeIntLaws.le, ``SafeIntLaws.ofSafeInt, ``SafeIntLaws.toSafeInt_inRange,
    ``SpecialValueLaws.safe_finite, ``SpecialValueLaws.isNaN_nan, ``SpecialValueLaws.isNaN_posInf,
    ``SpecialValueLaws.isNaN_negInf, ``SpecialValueLaws.isFinite_not_nan,
    ``SpecialValueLaws.isFinite_posInf, ``SpecialValueLaws.isFinite_negInf, ``SpecialValueLaws.eq_refl,
    ``SpecialValueLaws.eq_symm, ``SpecialValueLaws.nan_eq, ``SpecialValueLaws.nan_lt,
    ``SpecialValueLaws.nan_le, ``SpecialValueLaws.lt_posInf, ``SpecialValueLaws.negInf_lt,
    ``SpecialValueLaws.nan_add, ``SpecialValueLaws.nan_sub, ``SpecialValueLaws.nan_mul,
    ``SpecialValueLaws.sub_posInf_posInf]

/-- The theorems that are about no section of ECMA-262. -/
def extras : List Group := [
  ⟨"The translator's monad", [``Proof.bind_ok, ``Proof.map_ok, ``Proof.ite_state, ``Proof.pure_ok,
    ``Proof.get_ok, ``Proof.reject_ne_ok, ``Proof.orReject_ok, ``Proof.tooDeep_ne_ok,
    ``Proof.requireFeature_ok, ``Proof.modify_ok, ``Proof.fuelLimit_ok, ``Proof.throw_ne_ok,
    ``Proof.set_ok, ``Proof.isolated_ok]⟩,
  ⟨"Lists and lookups", [``Proof.Forall₂.mono, ``Proof.Forall₂.append, ``Proof.Forall₂.map,
    ``Proof.FnRelIn.mono, ``Proof.nodup_map_eq, ``Proof.findSome_eq, ``Proof.lookup_rel,
    ``Proof.lookup_isSome, ``Proof.lookup_append_some, ``Proof.lookup_none_of_not_mem,
    ``Proof.lookup_append_none, ``Proof.lookup_append_mem]⟩,
  ⟨"TypeScript types, which JS does not have", [``Proof.narrow_has, ``Proof.translateInterface_ok]⟩,
  ⟨"How Lean reads the output", [``Proof.eval_value, ``Proof.checkName_ok, ``Proof.checkLocalName_ok,
    ``checkLocalName_not_interface]⟩,
  ⟨"Imports across editions", [``translateImport_edition]⟩,
  ⟨"The parser", [``Syntax.parseChars_eq_of_parsesTo, ``Syntax.TypeExpr.beq_iff,
    ``Syntax.TypeExpr.beqList_iff, ``Syntax.TypeExpr.beqOpt_iff, ``Syntax.Expr.beq_iff,
    ``Syntax.Expr.beqList_iff, ``Syntax.Property.beq_iff, ``Syntax.Property.beqList_iff,
    ``Syntax.Expr.beqOpt_iff, ``Syntax.VarDecl.beq_iff, ``Syntax.Stmt.beq_iff,
    ``Syntax.Stmt.beqList_iff, ``Syntax.Stmt.beqOpt_iff, ``Syntax.Param.beq_iff,
    ``Syntax.Param.beqList_iff, ``Syntax.Field.beq_iff, ``Syntax.Field.beqList_iff,
    ``Syntax.Decl.beq_iff, ``Syntax.Decl.beqList_iff, ``Syntax.Module.beq_iff]⟩,
  ⟨"Certificates: the encoders and decoders", [``Eval.encNull_some, ``Eval.encNull_none,
    ``Eval.decInt_int, ``Eval.decBool_bool, ``Eval.decNum_num, ``Eval.decStr_str, ``Eval.decList_list,
    ``Eval.decNull_some, ``Eval.decList_nil, ``Eval.decList_cons, ``Eval.decList_encList,
    ``Eval.decNull_encNull, ``Eval.decNull_null]⟩]

open Meta in
/-- The theorems of the TypeScript modules that the index does not list. A
theorem that Lean generates, such as an equation lemma, has no declaration in
the source, so the check leaves it out. -/
def unlisted : MetaM (List Name) := do
  let env ← getEnv
  let listed := everySection.theorems ++ sections.flatMap (·.theorems) ++ numberLaws ++
    extras.flatMap (·.theorems)
  let mut out := #[]
  for mod in env.header.moduleNames, data in env.header.moduleData do
    unless (`tolean.TypeScript).isPrefixOf mod do continue
    for n in data.constNames do
      if n.isInternalDetail || listed.contains n then continue
      let some (.thmInfo _) := env.find? n | continue
      if (← findDeclarationRanges? n).isNone then continue
      out := out.push n
  return out.toList

#eval show MetaM Unit from do
  let missing ← unlisted
  unless missing.isEmpty do
    throwError "the index does not list these theorems: {missing}"

end tolean.TypeScript.Coverage
