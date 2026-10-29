import Lean
import tolean.TypeScript.Certify
import tolean.TypeScript.EStateM
import tolean.TypeScript.Interpret
import tolean.TypeScript.Proof.Guard
import tolean.TypeScript.Proof.Link
import tolean.TypeScript.Syntax.Equality
import tolean.TypeScript.Syntax.Print
import tolean.TypeScript.Syntax.Source
import tolean.TypeScript.Syntax.Layout
import tolean.TypeScript.Syntax.RoundTripDecl
import tolean.TypeScript.Syntax.RoundTripLex
import tolean.TypeScript.Syntax.ParseWF
import tolean.TypeScript.Syntax.RoundTripText
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
rename breaks the build. The checks at the end of this file fail when a
theorem of the TypeScript modules is in no list, so a new theorem must find
its place here, and when a file under `tolean/TypeScript` is not imported
here, so a new file cannot hide its theorems from the first check.

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
    ``Proof.programTranslation_rel, ``Proof.expr_sound, ``Proof.stmts_sound, ``Proof.decls_sound]⟩

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
    [``Proof.loop_sim, ``Proof.runFold_foldl]⟩,
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
  ⟨"The parser's round trip: types, as tokens",
    [``Syntax.types_reads, ``Syntax.parseType_union, ``Syntax.parseType_plain,
    ``Syntax.parseArrayType_reads, ``Syntax.parsePrimaryType_ref, ``Syntax.parsePrimaryType_paren,
    ``Syntax.parsePrimaryType_keyword, ``Syntax.parsePrimaryType_name, ``Syntax.parsePrimaryType_simple, ``Syntax.reads_one,
    ``Syntax.iterate_brackets, ``Syntax.iterate_brackets_goal, ``Syntax.iterate_sep,
    ``Syntax.iterate_sepBefore, ``Syntax.iterate_stop, ``Syntax.unionStep_go,
    ``Syntax.unionStep_stop, ``Syntax.arrayWF_split, ``Syntax.arrayWF_head, ``Syntax.arrayOf_array,
    ``Syntax.brackets_succ, ``Syntax.length_brackets, ``Syntax.tokens_ref, ``Syntax.tokens_union,
    ``Syntax.tokens_union_one, ``Syntax.wordsOf_eq, ``Syntax.separated_flatten,
    ``Syntax.joined_cons, ``Syntax.length_joined, ``Syntax.length_sepBefore,
    ``Syntax.eraseAll_append, ``Syntax.length_eraseAll, ``Syntax.allWF_iff, ``Syntax.allArrayWF_iff,
    ``Syntax.height_le_heightOf, ``Syntax.followsType_cons, ``Syntax.followsType_punct,
    ``Syntax.followsArray_punct, ``Syntax.punct_ne, ``Syntax.leaves_advance,
    ``Syntax.Leaves.toKept, ``Syntax.Leaves.refl, ``Syntax.leaves_trans, ``Syntax.Leaves.rest_eq,
    ``Syntax.Leaves.left_eq,
    ``Syntax.instReflBEqTokenKind,
    ``Syntax.instLawfulBEqTokenKind, ``Syntax.Parse.bind_ok, ``Syntax.Parse.ite_state,
    ``Syntax.Parse.pure_ok, ``Syntax.Parse.get_ok, ``Syntax.Parse.failAt_ne_ok,
    ``Syntax.Parse.unexpected_ne_ok, ``Syntax.Parse.peek_eq, ``Syntax.Parse.peekAt_eq,
    ``Syntax.Parse.advance_eq, ``Syntax.Parse.advance_cons, ``Syntax.Parse.expectPunct_ok,
    ``Syntax.Parse.budget_eq, ``Syntax.Parse.iterate_succ,
    ``Syntax.noBreak_of]⟩,
  ⟨"The parser's round trip: expressions, as tokens",
    [``Syntax.closesTypeArguments_kinds, ``Syntax.Touching.kinds, ``Syntax.parsePrimary_simple,
    ``Syntax.parsePrimary_ident, ``Syntax.peekBinaryOp_separator, ``Syntax.peekAssignOp_separator,
    ``Syntax.endsAssign_separator, ``Syntax.Touching.append_split, ``Syntax.Touching.cons_one,
    ``Syntax.Expr.first, ``Syntax.Parse.peekAt_rest, ``Syntax.startsExpr_ne,
    ``Syntax.peekBinaryOp_op, ``Syntax.peekAssignOp_op,
    ``Syntax.peekBinaryOp_assignOp, ``Syntax.peekBinaryOp_question, ``Syntax.endsPostfix_of,
    ``Syntax.binOp_head, ``Syntax.assignOp_head, ``Syntax.endsBin_binOp, ``Syntax.endsCond_assignOp,
    ``Syntax.endsBin_question, ``Syntax.EndsBin.mono, ``Syntax.Parse.spanFrom_eq,
    ``Syntax.Parse.requireFeature_ok, ``Syntax.Parse.skip_ok, ``Syntax.Parse.iterate_true,
    ``Syntax.Parse.iterate_false, ``Syntax.tail_sub, ``Syntax.ReadsW.weaken,
    ``Syntax.Touching.nil, ``Syntax.iterate_list,
    ``Syntax.Expr.wordsOf_eq, ``Syntax.Property.wordsOf_eq, ``Syntax.Expr.eraseAll_eq,
    ``Syntax.Property.eraseAll_eq, ``Syntax.Expr.listAfter, ``Syntax.Property.listAfter,
    ``Syntax.length_items, ``Syntax.Expr.start, ``Syntax.refuseArgument_ok, ``Syntax.refuseElement_ok,
    ``Syntax.endsItem_assign, ``Syntax.Touching.enclosed, ``Syntax.parseArguments_reads,
    ``Syntax.Parse.bind_eq, ``Syntax.Parse.pure_eq, ``Syntax.Parse.discard_eq,
    ``Syntax.parseArrayLiteral_reads, ``Syntax.Property.start, ``Syntax.parseProperty_reads,
    ``Syntax.parseObjectLiteral_reads, ``Syntax.expression_reads, ``Syntax.refuseArrowLookalike_ok,
    ``Syntax.notFirst_cons, ``Syntax.parsePrimary_paren, ``Syntax.words_lhs, ``Syntax.wf_lhsHead,
    ``Syntax.afterOK_lhsHead, ``Syntax.height_lhsHead, ``Syntax.length_propertyName, ``Syntax.lhsSteps_le,
    ``Syntax.refuseSplitMember_ok, ``Syntax.readPropertyName_ok,
    ``Syntax.lhsStep_member, ``Syntax.lhsStep_index, ``Syntax.lhsStep_call, ``Syntax.lhsStep_stop,
    ``Syntax.Touching.propertyName, ``Syntax.lhs_loop, ``Syntax.Touching.head,
    ``Syntax.parseLeftHandSide_reads, ``Syntax.Parse.pure_bind, ``Syntax.Expr.isSimpleTarget_erase,
    ``Syntax.isSimpleTarget_of_erase, ``Syntax.updateOp_symbol, ``Syntax.Expr.firstPrimary,
    ``Syntax.tokens_lhs, ``Syntax.head_append_of, ``Syntax.Expr.firstLhs, ``Syntax.wfAt_postfix_eq,
    ``Syntax.wfAt_unary_eq, ``Syntax.Expr.firstPostfix, ``Syntax.unaryOp_none, ``Syntax.updateOp_none,
    ``Syntax.unaryOp_symbol, ``Syntax.parsePostfix_reads, ``Syntax.parseUnary_reads, ``Syntax.BinOp.beq_eq,
    ``Syntax.words_bin, ``Syntax.wf_binHead, ``Syntax.afterOK_binHead, ``Syntax.height_binHead,
    ``Syntax.binSteps_le, ``Syntax.binSuffix_first, ``Syntax.Expr.isLogical_erase,
    ``Syntax.Expr.isCoalesce_erase, ``Syntax.isLogical_of_erase, ``Syntax.isCoalesce_of_erase,
    ``Syntax.notUnary_of_erase, ``Syntax.precedence_lt_exp, ``Syntax.binStep_stop, ``Syntax.Parse.ite_guard,
    ``Syntax.binStep_go, ``Syntax.leftOK_exp, ``Syntax.le_rhsPrec, ``Syntax.nextOp_left, ``Syntax.bin_loop,
    ``Syntax.parseBinary_reads, ``Syntax.wfAt_cond_eq, ``Syntax.wfAt_assign_eq, ``Syntax.ends_cond_eq,
    ``Syntax.parseConditional_reads, ``Syntax.isSimpleTarget_cond, ``Syntax.parseAssign_reads,
    ``Syntax.Expr.height_le_heightOf, ``Syntax.Property.height_le_heightOf, ``Syntax.Expr.allWF_iff,
    ``Syntax.Property.allWF_iff, ``Syntax.readsE_one, ``Syntax.parsePrimary_array,
    ``Syntax.parsePrimary_object, ``Syntax.primary_reads, ``Syntax.allRead_succ, ``Syntax.exprs_read_le,
    ``Syntax.exprs_read, ``Syntax.instLawfulBEqPos, ``Syntax.instReflBEqPos, ``Syntax.instLawfulBEqBinOp,
    ``Syntax.Neutral.nil, ``Syntax.Neutral.append, ``Syntax.Neutral.one, ``Syntax.Neutral.enclosed,
    ``Syntax.Neutral.cons, ``Syntax.Neutral.all, ``Syntax.Neutral.join, ``Syntax.neutral_binOp,
    ``Syntax.neutral_assignOp, ``Syntax.neutral_unaryOp, ``Syntax.neutral_updateOp,
    ``Syntax.neutral_propertyName, ``Syntax.neutral_key, ``Syntax.Expr.neutral,
    ``Syntax.Expr.neutralAll, ``Syntax.Property.neutral, ``Syntax.Property.neutralAll,
    ``Syntax.AfterEquiv.prepend, ``Syntax.AfterEquiv.closer, ``Syntax.neutral_args,
    ``Syntax.Expr.afterOK_congr, ``Syntax.Expr.afterOKList_congr, ``Syntax.Property.afterOK_congr,
    ``Syntax.Property.afterOKList_congr, ``Syntax.afterOK_semicolon, ``Syntax.length_symbol_binOp,
    ``Syntax.length_symbol_assignOp, ``Syntax.length_symbol_unaryOp, ``Syntax.Expr.tokens_array,
    ``Syntax.Expr.tokens_object, ``Syntax.Expr.tokens_paren, ``Syntax.Expr.tokens_member,
    ``Syntax.Expr.tokens_index, ``Syntax.Expr.tokens_call, ``Syntax.Expr.tokens_unary,
    ``Syntax.Expr.tokens_prefix, ``Syntax.Expr.tokens_postfix, ``Syntax.Expr.tokens_binary,
    ``Syntax.Expr.tokens_cond, ``Syntax.Expr.tokens_assign, ``Syntax.Property.tokens_keyValue,
    ``Syntax.Expr.height_le, ``Syntax.Expr.heightOf_le, ``Syntax.Property.height_le,
    ``Syntax.Property.heightOf_le, ``Syntax.need_le_budget, ``Syntax.parseAssign_budget,
    ``Syntax.parseExpression_budget,
    ``Syntax.Placed.chained, ``Syntax.Placed.next, ``Syntax.Touching.after_lineBreak,
    ``Syntax.flatten_callBreak, ``Syntax.Touching.after_callBreak, ``Syntax.propertyName_ne_paren]⟩,
  ⟨"The parser's round trip: statements, as tokens",
    [``Syntax.Stmt.lines_words, ``Syntax.Stmt.linesOf_words, ``Syntax.Laid.append, ``Syntax.Laid.one,
    ``Syntax.Laid.cons, ``Syntax.TypeExpr.tokens_paren, ``Syntax.TypeExpr.tokens_array,
    ``Syntax.TypeExpr.height_le, ``Syntax.TypeExpr.heightOf_le, ``Syntax.TypeExpr.heightOf_le_bars,
    ``Syntax.parseType_budget, ``Syntax.readName_ok, ``Syntax.endStatement_semi, ``Syntax.VarKind.word_eq,
    ``Syntax.followsType_eq_semi, ``Syntax.varDecl_ss, ``Syntax.varDecl_ns, ``Syntax.varDecl_sn,
    ``Syntax.varDecl_nn, ``Syntax.parseVarDecl_reads,
    ``Syntax.stmt_empty, ``Syntax.stmt_jump, ``Syntax.stmt_return_none, ``Syntax.stmt_return_some,
    ``Syntax.parseStatement_expr, ``Syntax.stmt_expr, ``Syntax.stmt_varDecl, ``Syntax.Laid.kinds,
    ``Syntax.Stmt.first, ``Syntax.Laid.first, ``Syntax.parseBranch_reads, ``Syntax.Stmt.linesOf_wordLines,
    ``Syntax.next_not_else, ``Syntax.Laid.length_le, ``Syntax.block_loop, ``Syntax.Stmt.eraseAll_eq,
    ``Syntax.parseBlock_reads, ``Syntax.stmt_block, ``Syntax.afterOK_closer, ``Syntax.EndsExpr.closer,
    ``Syntax.Touching.keywordParen, ``Syntax.stmt_if_none, ``Syntax.stmt_if_some,
    ``Syntax.Parse.withLoop_ok, ``Syntax.leaves_withLoop, ``Syntax.stmt_while, ``Syntax.parseForOf_reads,
    ``Syntax.stmt_for, ``Syntax.Stmt.allWF_iff, ``Syntax.Stmt.depth_le_depthOf, ``Syntax.allStmts_succ,
    ``Syntax.stmts_read_le, ``Syntax.stmts_read,
    ``Syntax.Expr.firstWord, ``Syntax.Touching.after_one]⟩,
  ⟨"The parser's round trip: declarations and modules, as tokens",
    [``Syntax.followsType_item, ``Syntax.parseParam_reads, ``Syntax.Stmt.wordLines_if_none,
    ``Syntax.Stmt.wordLines_if_some, ``Syntax.Stmt.tokens_length_cons, ``Syntax.Stmt.tokensOf,
    ``Syntax.Stmt.tokens_eq, ``Syntax.Stmt.depth_lt, ``Syntax.Stmt.depthOf_le,
    ``Syntax.Stmt.need_le_budget, ``Syntax.parseStatement_budget, ``Syntax.parseBlock_budget,
    ``Syntax.Parse.modify_eq, ``Syntax.leaves_inFunction, ``Syntax.listAfter_true,
    ``Syntax.params_reads, ``Syntax.parseFunction_reads,
    ``Syntax.parseTypeAlias_reads, ``Syntax.second_append, ``Syntax.Expr.tokens_ne_nil,
    ``Syntax.notIdent_binOp, ``Syntax.notIdent_assignOp, ``Syntax.Expr.second, ``Syntax.parseField_plain,
    ``Syntax.parseField_opt, ``Syntax.parseField_ro, ``Syntax.parseField_reads,
    ``Syntax.Field.first, ``Syntax.field_loop, ``Syntax.Laid.length_fields, ``Syntax.parseInterface_reads,
    ``Syntax.Touching.importName, ``Syntax.importStep_ok, ``Syntax.import_loop, ``Syntax.parseImport_reads,
    ``Syntax.Stmt.declStart, ``Syntax.parseDecl_stmt, ``Syntax.parseDecl_import,
    ``Syntax.parseDecl_typeAlias, ``Syntax.parseDecl_interface, ``Syntax.parseDecl_function,
    ``Syntax.parseDecl_exportedVar, ``Syntax.parseDecl_reads, ``Syntax.Decl.first,
    ``Syntax.Module.lines_words, ``Syntax.Laid.length_decls, ``Syntax.decl_loop, ``Syntax.module_reads]⟩,
  ⟨"The parser's round trip: the lexer's part",
    [``Syntax.Lex.bind_ok, ``Syntax.Lex.bind_eq, ``Syntax.Lex.okOf_ok, ``Syntax.Lex.okOf_bind,
    ``Syntax.Lex.okOf_eq_some, ``Syntax.Lex.okOf_pure, ``Syntax.Lex.okOf_map, ``Syntax.Lex.okOf_ite,
    ``Syntax.Lex.skipped_zero, ``Syntax.Lex.skipped_skipped, ``Syntax.Lex.skipped_rest,
    ``Syntax.Lex.skipped_i, ``Syntax.Lex.skipped_target, ``Syntax.Lex.skipped_size,
    ``Syntax.Lex.skipped_tokens, ``Syntax.Lex.skipped_newline, ``Syntax.Lex.skipChar_eq,
    ``Syntax.Lex.peekChar_eq, ``Syntax.Lex.get_eq, ``Syntax.Lex.budget_eq, ``Syntax.Lex.here_eq,
    ``Syntax.Lex.okOf_failFrom, ``Syntax.Lex.okOf_skipChar, ``Syntax.Lex.okOf_peekChar,
    ``Syntax.Lex.okOf_get, ``Syntax.Lex.okOf_budget, ``Syntax.Lex.Kept.tokens, ``Syntax.Lex.Kept.size,
    ``Syntax.Lex.Kept.target, ``Syntax.Lex.Kept.fits, ``Syntax.Lex.Kept.refl, ``Syntax.Lex.Kept.trans,
    ``Syntax.Lex.Keeps.kept, ``Syntax.Lex.keeps_pure, ``Syntax.Lex.keeps_bind, ``Syntax.Lex.keeps_ite,
    ``Syntax.Lex.keeps_get, ``Syntax.Lex.keeps_throw, ``Syntax.Lex.keeps_skipChar,
    ``Syntax.Lex.keeps_skipLineBreak, ``Syntax.Lex.keeps_peekChar, ``Syntax.Lex.keeps_here,
    ``Syntax.Lex.keeps_budget, ``Syntax.Lex.keeps_failFrom, ``Syntax.Lex.keeps_outOfFuel,
    ``Syntax.Lex.keeps_takeAs, ``Syntax.Lex.keeps_skipLineComment, ``Syntax.Lex.keeps_skipBlockComment,
    ``Syntax.Lex.keeps_skipTrivia, ``Syntax.Lex.keeps_readHex, ``Syntax.Lex.keeps_readBracedHex,
    ``Syntax.Lex.keeps_readCodeUnit, ``Syntax.Lex.keeps_readCodePoint, ``Syntax.Lex.keeps_readEscape,
    ``Syntax.Lex.keeps_readStringBody, ``Syntax.Lex.readMoreDigits_eq, ``Syntax.Lex.readDigits_eq,
    ``Syntax.Lex.fits_skipped, ``Syntax.Lex.numEnd_eq, ``Syntax.Lex.numExp_eq,
    ``Syntax.Lex.numDot_eq, ``Syntax.Lex.lexNumber_eq, ``Syntax.Lex.moreDigits_le, ``Syntax.Lex.digitsOf_le,
    ``Syntax.Lex.endOf_some, ``Syntax.Lex.expOf_some, ``Syntax.Lex.dotOf_some, ``Syntax.Lex.numberOf_some,
    ``Syntax.Lex.numberOf_ok, ``Syntax.Lex.StopsAlike.look, ``Syntax.Lex.look_len,
    ``Syntax.Lex.look_eq, ``Syntax.Lex.moreDigits_pos, ``Syntax.Lex.moreDigits_frame,
    ``Syntax.Lex.digitsOf_frame, ``Syntax.Lex.endOf_frame, ``Syntax.Lex.endOf_le, ``Syntax.Lex.expOf_le,
    ``Syntax.Lex.expOf_frame, ``Syntax.Lex.dotOf_frame, ``Syntax.Lex.dotOf_le, ``Syntax.Lex.radixOf_none,
    ``Syntax.Lex.radixOf_blank, ``Syntax.Lex.numberOf_frame, ``Syntax.Lex.foldl_push_toList,
    ``Syntax.Lex.charsToString_toList, ``Syntax.Lex.readWhile_eq, ``Syntax.Lex.forIn_range_skip,
    ``Syntax.Lex.forIn_skip, ``Syntax.Lex.find?_congr, ``Syntax.Lex.startsWith_blank,
    ``Syntax.Lex.punctuators_first, ``Syntax.Lex.punctuators_blank, ``Syntax.Lex.lexPunct_find,
    ``Syntax.Lex.lexPunct_eq, ``Syntax.Lex.lexPunct_gt, ``Syntax.Lex.quote_toList,
    ``Syntax.Lex.length_escChars, ``Syntax.Lex.readStringBody_char, ``Syntax.Lex.readStringBody_quote,
    ``Syntax.Lex.lexKind_string, ``Syntax.Lex.identName_toList, ``Syntax.Lex.blank_not_identPart,
    ``Syntax.Lex.lexKind_name, ``Syntax.Lex.punct_start, ``Syntax.Lex.punct_second,
    ``Syntax.Lex.lexKind_punct, ``Syntax.Lex.lexKind_gt, ``Syntax.Lex.fits_start,
    ``Syntax.Lex.numberOK_some, ``Syntax.Lex.numberOK_of, ``Syntax.Lex.not_trivia, ``Syntax.Lex.digit_mem,
    ``Syntax.Lex.digit_not_identStart, ``Syntax.Lex.lexKind_number, ``Syntax.Lex.reserved_identName,
    ``Syntax.Lex.lexKind_text, ``Syntax.Lex.noTrivia_text, ``Syntax.Lex.skipTrivia_stop,
    ``Syntax.Lex.skipTrivia_gap, ``Syntax.Lex.modify_eq, ``Syntax.Lex.blank_length,
    ``Syntax.Lex.lexAll_token, ``Syntax.Lex.lexAll_end, ``Syntax.Lex.word_text, ``Syntax.Lex.lexAll_word,
    ``Syntax.Lex.wordsText_break, ``Syntax.Lex.wordsText_one, ``Syntax.Lex.wordsText_cons_break,
    ``Syntax.Lex.wordsText_cons, ``Syntax.Lex.lexAll_words, ``Syntax.Lex.pushn_toList,
    ``Syntax.Lex.render_cons, ``Syntax.Lex.lexAll_lines,
    ``Syntax.Lex.kept_skipped, ``Syntax.Lex.lexPunct_ok, ``Syntax.Lex.lexKind_ok, ``Syntax.Lex.lexAll_ok,
    ``Syntax.Lex.lexChars_tokens, ``Syntax.lexChars_render, ``Syntax.lexChars_ok_kinds,
    ``Syntax.lexChars_last_eof]⟩,
  ⟨"The parser's round trip: every tree that the parser gives is well formed",
    [``Syntax.Kept.eof_eq, ``Syntax.Kept.inFunction_eq, ``Syntax.Kept.loopDepth_eq, ``Syntax.Kept.target_eq,
    ``Syntax.GaveE.ready, ``Syntax.GaveE.kept, ``Syntax.GaveE.tokens, ``Syntax.GaveE.wf, ``Syntax.GaveE.after,
    ``Syntax.GaveE.ok, ``Syntax.GaveArgs.ready, ``Syntax.GaveArgs.kept, ``Syntax.GaveArgs.tokens,
    ``Syntax.GaveArgs.wf, ``Syntax.GaveArgs.after, ``Syntax.GaveArgs.ok,
    ``Syntax.closesKinds_skel, ``Syntax.skel_append, ``Syntax.closesKinds_of_skel, ``Syntax.closesKinds_end,
    ``Syntax.follows_end, ``Syntax.Follows.prefix, ``Syntax.Kept.refl, ``Syntax.Kept.trans, ``Syntax.WordsOK.nil,
    ``Syntax.WordsOK.append, ``Syntax.WordsOK.cons, ``Syntax.WordsOK.word, ``Syntax.ok_punct, ``Syntax.ok_keyword,
    ``Syntax.binOp_ok, ``Syntax.assignOp_ok, ``Syntax.Ready.more, ``Syntax.Ready.suffix,
    ``Syntax.Ready.past, ``Syntax.Kept.past, ``Syntax.advance_past, ``Syntax.ok_unique,
    ``Syntax.expectPunct_inv, ``Syntax.readName_inv, ``Syntax.outOfFuel_ne_ok, ``Syntax.iterate_inv,
    ``Syntax.Ready.cons, ``Syntax.advance_inv,
    ``Syntax.primaryWF_arrayWF, ``Syntax.arrayWF_wf, ``Syntax.Ready.tok, ``Syntax.wordsOK_iff,
    ``Syntax.WordsOK.separated, ``Syntax.WordsOK.wordsOf, ``Syntax.skip_two,
    ``Syntax.arrayStep_inv, ``Syntax.push_ok, ``Syntax.unionStep_inv, ``Syntax.typeArgStep_inv,
    ``Syntax.failAt_bind_ne_ok, ``Syntax.unexpected_bind_ne_ok, ``Syntax.both, ``Syntax.both_left,
    ``Syntax.both_right, ``Syntax.types_give, ``Syntax.skip_inv,
    ``Syntax.peekAt_real, ``Syntax.ofSymbol_binOp, ``Syntax.ofSymbol_assignOp, ``Syntax.symbol_binOp_punct,
    ``Syntax.Ready.notLast, ``Syntax.peekGreater_eq, ``Syntax.peek_punct, ``Syntax.list_two, ``Syntax.list_three,
    ``Syntax.list_four, ``Syntax.greater_inv, ``Syntax.peekBinaryOp_inv, ``Syntax.symbol_assignOp_punct,
    ``Syntax.peekAssignOp_inv, ``Syntax.unaryOp_inv, ``Syntax.updateOp_inv, ``Syntax.get_bind,
    ``Syntax.refuseTypeArgumentLookalike_inv, ``Syntax.requireFeature_inv, ``Syntax.peek_eq',
    ``Syntax.refuseArrowLookalike_inv, ``Syntax.refuseAsyncArrowLookalike_inv, ``Syntax.check_inv,
    ``Syntax.refuseSplitMember_inv, ``Syntax.readPropertyName_inv, ``Syntax.joined_snoc, ``Syntax.ListAfter.snoc,
    ``Syntax.Expr.afterOKList_of, ``Syntax.Property.afterOKList_of, ``Syntax.skel_joined_snoc, ``Syntax.listStep_inv,
    ``Syntax.wfAt_lhs_of_primary, ``Syntax.wfAt_postfix_of_lhs, ``Syntax.wfAt_unary_of_postfix,
    ``Syntax.wfAt_bin_of_unary, ``Syntax.wfAt_bin_mono, ``Syntax.wfAt_cond_of_bin, ``Syntax.wfAt_assign_of_cond,
    ``Syntax.wordsOK_enclose, ``Syntax.wordsOK_callBreak, ``Syntax.Expr.wordsOK_of, ``Syntax.Property.wordsOK_of,
    ``Syntax.propertyName_ok, ``Syntax.GaveE.lift, ``Syntax.head_append2,


    ``Syntax.head_append_ne, ``Syntax.parseExpression_gives,
    ``Syntax.symbol_assignOp_head, ``Syntax.symbol_binOp_head, ``Syntax.assign_tail, ``Syntax.parseAssign_gives,
    ``Syntax.skel_cons, ``Syntax.parseConditional_gives, ``Syntax.seq_inv, ``Syntax.fail_inv,
    ``Syntax.BinOp.precedence_le, ``Syntax.BinOp.precedence_twelve, ``Syntax.leftOK_of, ``Syntax.mixing_of,
    ``Syntax.binaryStep_inv, ``Syntax.parseBinary_gives, ``Syntax.parseUnary_gives, ``Syntax.parsePostfix_gives,
    ``Syntax.list_inv, ``Syntax.GivesE.item, ``Syntax.refuseArgument_inv, ``Syntax.refuseElement_inv,
    ``Syntax.tokens_args, ``Syntax.bracketed, ``Syntax.parseArguments_gives, ``Syntax.parseArrayLiteral_gives,
    ``Syntax.skel_propertyName, ``Syntax.keyValue_tail, ``Syntax.parseProperty_gives,
    ``Syntax.parseObjectLiteral_gives, ``Syntax.leaf_gives, ``Syntax.parsePrimary_gives, ``Syntax.seq_same,
    ``Syntax.skel_one, ``Syntax.lhsStep_inv, ``Syntax.parseLeftHandSide_gives, ``Syntax.exprs_give,
    ``Syntax.wordsOK_append_iff, ``Syntax.wordsOK_cons_iff, ``Syntax.wordsOK_nil_iff, ``Syntax.readName_words,
    ``Syntax.VarKind.word_ok, ``Syntax.exportWords_ok, ``Syntax.typeAnnotation_ok, ``Syntax.VarDecl.wordsOK, ``Syntax.Param.wordsOK,
    ``Syntax.Field.wordsOK, ``Syntax.ImportName.wordsOK, ``Syntax.StmtOK.one, ``Syntax.StmtOK.head,
    ``Syntax.StmtOK.varDecl, ``Syntax.StmtOK.exprStmt, ``Syntax.StmtOK.retNone, ``Syntax.StmtOK.retSome,
    ``Syntax.StmtOK.brk, ``Syntax.StmtOK.cont, ``Syntax.StmtOK.empty, ``Syntax.StmtOK.ifThen, ``Syntax.StmtOK.ifElse,
    ``Syntax.StmtOK.forOf, ``Syntax.StmtOK.while, ``Syntax.linesOf_ok, ``Syntax.StmtOK.block,
    ``Syntax.endStatement_inv, ``Syntax.varDecl_tail, ``Syntax.parseVarDecl_inv, ``Syntax.blockStep_inv,
    ``Syntax.parseBlock_gives, ``Syntax.parseBranch_gives,
    ``Syntax.withLoop_inv, ``Syntax.parseExpressionStatement_inv, ``Syntax.pass_inv, ``Syntax.choose_inv,
    ``Syntax.parseForOf_inv, ``Syntax.parenTest_inv, ``Syntax.exprStmt_gives, ``Syntax.parseStatement_gives,
    ``Syntax.stmts_give, ``Syntax.DeclOK.import, ``Syntax.DeclOK.function, ``Syntax.DeclOK.interface,
    ``Syntax.DeclOK.typeAlias, ``Syntax.DeclOK.exportedVar, ``Syntax.DeclOK.stmt, ``Syntax.listStep_wf,
    ``Syntax.blockStep_wf, ``Syntax.advance_ready, ``Syntax.discard_advance_ready, ``Syntax.Refuses.bind,
    ``Syntax.unexpected_refuses, ``Syntax.refuseImport_refuses, ``Syntax.pass_err,
    ``Syntax.fail_err, ``Syntax.seq_advance, ``Syntax.parseParam_wf, ``Syntax.parseField_wf,
    ``Syntax.parseBlock_block, ``Syntax.parseFunction_wf, ``Syntax.parseInterface_wf, ``Syntax.parseTypeAlias_wf,
    ``Syntax.importStep_wf, ``Syntax.parseImport_wf, ``Syntax.parseDecl_wf, ``Syntax.declStep_wf,
    ``Syntax.parseModule_wf, ``Syntax.parseTokens_wf]⟩,
  ⟨"The parser's round trip: on source text",
    [``Syntax.breaksOK_append, ``Syntax.breaksOK_of_ne, ``Syntax.Fine.append,
    ``Syntax.Fine.word, ``Syntax.Fine.cons, ``Syntax.fine_separated, ``Syntax.fine_enclose, ``Syntax.nil_not_mem_separated,
    ``Syntax.symbol_ne, ``Syntax.TypeExpr.no_lineBreak, ``Syntax.TypeExpr.no_lineBreakAll,
    ``Syntax.Fine.call, ``Syntax.propertyName_ne, ``Syntax.Expr.fine, ``Syntax.Expr.fineAll, ``Syntax.Property.fine,
    ``Syntax.Property.fineAll, ``Syntax.LineOK.append, ``Syntax.LineOK.nil, ``Syntax.Fine.line, ``Syntax.LineOK.word,
    ``Syntax.LineOK.cons, ``Syntax.TypeExpr.line, ``Syntax.VarKind.word_ne, ``Syntax.typeAnnotation_line, ``Syntax.VarDecl.line,
    ``Syntax.Stmt.lineOK, ``Syntax.Stmt.lineOKAll, ``Syntax.Fine.ofLine, ``Syntax.exportWords_line,
    ``Syntax.Decl.lineOK, ``Syntax.Module.breaksOK, ``Syntax.source_reads, ``Syntax.parseChars_reads]⟩,
  ⟨"The parser", [``Syntax.parseChars_eq_of_parsesTo, ``Syntax.TypeExpr.beq_iff,
    ``Syntax.TypeExpr.beqList_iff, ``Syntax.TypeExpr.beqOpt_iff, ``Syntax.Expr.beq_iff,
    ``Syntax.Expr.beqList_iff, ``Syntax.Property.beq_iff, ``Syntax.Property.beqList_iff,
    ``Syntax.Expr.beqOpt_iff, ``Syntax.VarDecl.beq_iff, ``Syntax.Stmt.beq_iff,
    ``Syntax.Stmt.beqList_iff, ``Syntax.Stmt.beqOpt_iff, ``Syntax.Param.beq_iff,
    ``Syntax.Param.beqList_iff, ``Syntax.Field.beq_iff, ``Syntax.Field.beqList_iff,
    ``Syntax.Decl.beq_iff, ``Syntax.Decl.beqList_iff, ``Syntax.Module.beq_iff]⟩,
  ⟨"Certificates: the check that the translator gives the tree", [``Proof.translatesTo_ok,
    ``Output.Expr.beq_iff, ``Output.Expr.beqList_iff, ``Output.Expr.beqFields_iff]⟩,
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

/-- The modules under `tolean/TypeScript` that this file does not import.
Lake builds the library from the package root, so the path is relative. -/
def unimported : MetaM (List Name) := do
  let env ← getEnv
  let files ← System.FilePath.walkDir "tolean/TypeScript"
  let modules := files.toList.filterMap fun f =>
    if f.extension != some "lean" then none
    else some ((f.withExtension "").components.foldl Name.str .anonymous)
  return modules.filter fun m => m != `tolean.TypeScript.Spec.Coverage && !env.header.moduleNames.contains m

#eval show MetaM Unit from do
  let missing ← unimported
  unless missing.isEmpty do
    throwError "the index does not import these modules, so it cannot check their theorems: {missing}"

end tolean.TypeScript.Coverage
