# Galette: agent and contributor notes

Galette is a Rocq port of the CakeML Pancake compiler and its correctness
theorems, restricted to the RISC-V backend. The reference is the HOL4 source
in the read-only `../flapjack` checkout: `../flapjack/cakeml` (CakeML,
including `pancake/`) and `../flapjack/HOL` (HOL4, including the L3 RISC-V
model). Flapjack's Lean port is a convenient second opinion, but **HOL is the
reference**. Do not modify `../flapjack`.

Goals, in priority order:

1. **Same-looking statements and definitions.** A ported declaration must be
   recognisably the HOL one: same name (Rocq naming may only differ where HOL
   names are illegal Rocq identifiers), same arguments in the same order,
   same constructors in the same order, same hypotheses and conclusion.
2. **Same bytes.** The extracted compiler must produce, byte for byte, the
   output of `cake --pancake --target=riscv` (the oracle digests are
   recorded in `../flapjack/scripts/parity-small-corpus.json` and
   `../flapjack/scripts/guest-parity.json`).

## Build

    dune build                               # all theories
    python3 scripts/check-hol-refs.py --kernel   # bookkeeping (see below)

Rocq 9.3 (`rocq-prover` opam package). Libraries are deliberately few; see
README.md for the dependency policy.

## Layout: one counterpart file per HOL script

HOL script `<dir>/<name>Script.sml` is ported to
`theories/<dir>/<name>.v` (characters of `<dir>` outside `[A-Za-z0-9_]` become
`_`; e.g. `HOL/src/n-bit/wordsScript.sml` -> `theories/HOL/src/n_bit/words.v`),
giving the Rocq module `Galette.<dir>.<name>`. A large script may be split
into `theories/<dir>/<name>/*.v`, named after HOL's own theorem groups. No
catch-all "bridge"/"adapter"/"misc" modules collecting fragments of several
scripts. Galette-only infrastructure (no HOL original) lives at the top of
`theories/` (e.g. `Base.v`) and says so in its header.

## Bookkeeping: `(*! HOL ... *)` tags

Every Rocq declaration that ports a HOL declaration is immediately preceded
(a docstring may sit in between) by

    (*! HOL "cakeml/pancake/panLangScript.sml" "shape" *)

citing the path relative to the reference checkout and the **exact** HOL
declaration name (`foo_def` for `Definition foo_def:`, the theorem name, or
the datatype name). If the script declares that name twice, add the line:
`(*! HOL "..." "name" 123 *)`. `scripts/check-hol-refs.py` enforces:

- the cited HOL file exists and declares the name;
- the tag is in the counterpart file (or its directory);
- **one HOL declaration has at most one Rocq translation** -- never add a
  second translation of something already tagged; reuse it (find it with
  `scripts/check-hol-refs.py --mapping | grep NAME`);
- every tag has a row in `docs/HOL-THEOREM-MAP.json`
  (`--update-manifest` adds new rows as `pending_review`);
- `--kernel`: every tagged Rocq name exists in the compiled library.

Manifest statuses: `pending_review` (tagged, not yet compared line-by-line),
`reviewed_exact` (compared; reviewer note required), `documented_mismatch`.
A successful build is not a review.

Splitting a large theorem along HOL's own case structure: each piece is tagged
`(*! HOL "..." "name" case "Skip" *)` and has the same hypotheses and
conclusion shape as the HOL theorem plus induction hypotheses only; a main
(untagged-case) translation assembles them.

**Name clashes.** HOL keeps constants and theorems in separate namespaces;
Rocq does not. When a HOL theorem has the name of a constant (e.g. listTheory's
theorem `MAP` characterising the constant `MAP`), the Rocq theorem is named
`<NAME>_thm`; the tag still cites the exact HOL name.

**Type/constructor clashes.** HOL keeps types and constructors apart too;
when a HOL type has a constructor's name (L3's `ArithI`), the Rocq type is
`<NAME>_ty`.

**A tag is a claim of sameness.** Before tagging, compare definitions,
quantified variables, hypotheses, side conditions, conclusions, and carrier
types (constructor arity, field types, word widths). If something differs,
do not tag; explain the difference in the docstring instead.

## Carrier conventions (how HOL types are represented)

These are fixed so that no declaration needs a representation qualifier.

| HOL | Rocq |
| --- | --- |
| `bool` (in code) | `bool`; in theorem statements coerced to `Prop` by `is_true` |
| predicates defined by quantifiers | `Prop` |
| `num` | `N` (binary, so concrete numbers like `dimword(:64)` compute in the kernel; extracted to Zarith). Every file has `Open Scope N_scope`. Recursion on `SUC n` uses `num_rec` (arithmetic.v) and HOL's equations are proved |
| `int` | `Z` |
| `'a list`, `'a option`, `'a # 'b` | `list`, `option`, `*` |
| `char` | `ascii` |
| `string` (= `char list` in HOL) | `list ascii` (HOL's own type abbreviation), with string literals via `String Notation`; not Rocq's `String.string` |
| `ordering` | `ordering` (`LESS`/`EQUAL`/`GREATER`, ported from `ternaryComparisons`) |
| `mlstring` | `mlstring` with constructor `implode` (HOL's), `strlit` an abbreviation |
| `'a word` | `word a` with `a : nat` the width index, `dimindex a` as in HOL |
| `'a |-> 'b` | `fmap` (`theories/HOL/src/finite_maps/finite_map.v`) |
| `num_map`, `'a spt` | `spt` (`theories/HOL/src/finite_maps/sptree.v`) |
| `'a set` | `'a -> Prop`, with HOL's `pred_set` operations (`IN`, `INSERT`, `UNION`, ...) ported so statements read as in HOL |
| `ARB`, `@x. P x` | `ARB`, `select P` (`Base.v`) |
| HOL `=` tested in code | `decide (x = y)` via `EqDecision` |
| record `s with f := v` | Rocq record update (write out the record or use a `set_f` helper) |

HOL's logic is classical with extensionality and choice; `Base.v` imports the
corresponding Rocq axioms (excluded middle, epsilon, functional and
propositional extensionality, proof irrelevance). No other axioms. No
`Admitted` in committed code outside files explicitly marked as work in
progress; prefer leaving a declaration untagged to tagging an unproved one.

When HOL defines an operation non-computationally (e.g. words via `FCP`) but
evaluates it through `[compute]` theorems, the Rocq definition is the
computational one and HOL's defining equation is proved as a theorem carrying
the `_def` tag. The tagged statement must be HOL's.

## Porting definitions

- **Datatypes**: same constructors in the same order with the same argument
  types. HOL's `'a` word-width type variables become `{a : N}` parameters.
  Nested inductives (`exp list`) are fine; write the induction principle you
  need by hand.
- **Records**: a Rocq `Record` with HOL's field names in HOL's order. HOL
  `s with f := v` becomes the record rebuilt with one field changed; define
  a `set_<f>` helper or write the record out. If a field name clashes within a
  Rocq module (HOL allows duplicates across records), prefix it with the
  record type name (`<rec>_<field>`); document it in the record docstring.
- **Recursion**: structural `Fixpoint` when HOL's recursion is structural
  (use nested `fix` for list-nested recursion). Otherwise define with `Fix` on
  a well-founded measure (or a provably sufficient fuel) and prove HOL's
  equations as the tagged `_def` theorem. Recursion on `num` uses `num_rec`
  or binary recursion; never unary recursion over potentially large numbers.
  `Function` (rocq-core funind) is allowed.
- **Pairs and patterns**: HOL tupled arguments `f (x, y)` stay tupled.
  `case ... of` maps to `match`; HOL's catch-all/overlapping patterns need the
  same first-match semantics.
- **Monads**: CakeML's `do ... od` (option/state/exception) maps to explicit
  binds with the same monad definitions as HOL (port the monad's definitions,
  e.g. `ml_monadBase`, rather than using a different library).
- **Executable**: compiler code must not use `ARB`, `select`, `classical_dec`
  or `Classical.v` unless HOL's code does exactly that; extracted code that
  hits them fails at run time.
- **Shared files**: if you need something in a file you do not own, say so in
  your report instead of editing it.

## Porting semantics (clocked `evaluate` functions)

CakeML semantics define `evaluate` by well-founded recursion on
`(clock, program size)`, where later calls use the state returned by earlier
ones (`fix_clock`). Rocq's `Function` cannot handle this (nested recursion).
Use the recipe of `theories/cakeml/pancake/semantics/panSem.v`:

1. `evaluate_body go lower p s`: HOL's clauses with `go` for calls at the
   same clock bound (structurally smaller programs: `Seq`, `Dec`, `If`, ...)
   and `lower` for calls at a strictly smaller clock (loop iteration, function
   bodies, handlers).
2. `evaluate_c cf`: structural recursion on a clock fuel `cf` (outer) and the
   program (inner `fix go`), with `lower` = `evaluate_c (cf - 1)`;
   `evaluate (p, s) := evaluate_c (S clock) p s`.
3. `evaluate_body_ext`: every recursive call is smaller in HOL's measure
   (`eval_lt`), so bodies agreeing on smaller arguments agree; the Ltac loop
   there rewrites calls and case-splits scrutinees, then `cbn beta iota zeta`
   (without it the loop re-splits constructor redexes and explodes).
4. `evaluate_c_fuel` by well-founded induction on `eval_lt`, then
   `evaluate_eqn : evaluate (p, s) = evaluate_body evaluate evaluate p s`,
   from which HOL's `evaluate_def` clauses follow.

Run long proof searches with a memory watchdog (a runaway case split can
exhaust RAM): see the build commands in recent commit messages.

## Testing parity

Compiler definitions are extracted to OCaml (`extraction/`). Parity tests run
the extracted compiler on the fixtures listed in
`../flapjack/scripts/parity-small-corpus.json` and compare the sha256 of the
output with the recorded `cake` digest.

## Porting order

1. HOL library foundations used by the compiler (num/bit/words/list/
   finite_map/sptree/alignment/mlstring/misc).
2. Compiler definitions along the pipeline (parser -> pan_to_target ->
   backend -> lab_to_target -> riscv encoder -> export), reaching byte parity.
3. Semantics (panSem ... targetSem, L3 RISC-V model).
4. Correctness proofs, pass by pass, up to `pan_to_target_compile_semantics`.
