# Policy: what this repository assumes from AxiomMath/Stacks

**Decision.**  The formalization and results of
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) — the Axiom Math
formalization of the Stacks Project — **may be used freely** in this repository.  A
result of the Stacks Project that AxiomMath has formalized counts as available; we do
not re-prove it here merely to avoid depending on it.

**This is a policy change from the earlier rule.**  Until now the rule was "keep our
own proof, and tag a Stacks statement only where we have none".  The standing rule is
now the freer one: use Stacks freely, and **mark every use**.  Where a proof already
exists here it is kept — deleting a proved theorem to replace it with an assumption
would make the development depend on more, not less — but nothing new is proved here
merely because Stacks had not been assumed before.

**Current practice (28 November 2026).**  The geometric results are in the library `Spaces`,
which imports only AxiomMath's definition modules (`scripts/axiommath/spaces-imports.txt`).  Each
AxiomMath theorem a proof uses is a tagged hypothesis `…Input : Prop` (AxiomMath's statement
verbatim, its Stacks tag and declaration name) in the `Inputs.lean` of the area; the library
`SpacesVerified` discharges each by the theorem itself, so the final results are unconditional.
A result whose AxiomMath input lives in a module whose closure contains
`MilnorPatching.Relative` is proved in `SpacesVerified` directly.  The older layers
(`FourierMukai/Scheme/`, `StacksInterface`) are described below.

## How a use is marked

Three levels, coarse to fine:

1. **`results/ASSUMPTIONS.md`** — the ledger.  Every Stacks input has a row with its
   tag and a status: `P` (proved here), `N` (derived from an explicit Neeman input),
   **`S` (supplied by AxiomMath/Stacks)**, `R` (bibliographic, not consumed).
2. **`FourierMukai/Scheme/StacksInput.lean`** — the machine-readable register.  A
   `Prop`-valued field per assumed statement, in `RelativeFM.StacksInterface`, each
   carrying its tag number and the exact statement.  A file that consumes an assumed
   Stacks statement takes one of those fields as a hypothesis; the dependency is then
   visible in the theorem's type, not only in a comment.
3. **Module docstrings** — a file whose mathematics rests on a Stacks tag says so in
   its header, with the tag number.

A use is not marked by naming a tag in prose alone; it is marked by a field the
theorem depends on, or by a `S` row in the ledger.

## AxiomMath is a Lake dependency (since 26 November 2026)

AxiomMath/Stacks is required in `lakefile.toml`, pinned at
`f56a316ddf7a930906d88b78d6f9a2668cffd0cf` (Lean/Mathlib v4.35.0, the same dependency
revisions as this repository).  Nothing is copied from it.  It is used in two layers,
neither of which is a default build target:

* **`Spaces`** (directory `Spaces/`) imports only AxiomMath's **definitions**: the
  modules listed in `scripts/axiommath/spaces-imports.txt` (~2 000 AxiomMath modules,
  ~40 min to build on 4 cores).  An AxiomMath **theorem** that these imports do not
  provide is taken as a **tagged input**: a `Prop` in `Spaces/AxiomMathInputs.lean` or in a
  task's `Spaces/<Area>/Inputs.lean`
  whose docstring gives the Stacks tag and the AxiomMath declaration, and whose
  statement is AxiomMath's statement verbatim (same objects, same hypotheses).
* **`SpacesVerified`** (directory `SpacesVerified/`) imports the AxiomMath theorems
  themselves and proves every tagged input from the declaration it names.  The
  paper's results over algebraic spaces are stated there **unconditionally**; their
  `#print axioms` is within `propext`, `Classical.choice`, `Quot.sound`.  Building it
  compiles ~8 500 AxiomMath modules (~6 h on 4 cores, ~14 GB of memory: one module,
  `StacksFrontier.RingTheory.MilnorPatching.Relative`, peaks at ~13.6 GB); the
  orchestrator runs it.

The list of Stacks tags the papers use, with the AxiomMath declaration for each, is
[`results/AXIOMMATH_TAGS.md`](AXIOMMATH_TAGS.md); the fidelity audit of the definitions
is [`results/AXIOMMATH_MAP.md`](AXIOMMATH_MAP.md).  The older interface
`RelativeFM.StacksInterface` (`FourierMukai/Scheme/StacksInput.lean`) serves the
abstract and affine layers and is retired as their results are restated over spaces.

## If Axiom's repository enters Mathlib or Lean

Then the marks become imports, and the update is mechanical:

* replace a `StacksInput` field by the imported declaration of the same statement;
* delete the corresponding `S` row from the ledger and move it to `P` with a note that
  it now comes from the library;
* the theorems that took the field as a hypothesis lose it, since it is discharged by
  the instance.

Nothing else changes: no proof here is written against AxiomMath's *names*, only
against the statements recorded in the interface.  That is the reason for insisting
that each assumed statement be a `Prop` with its own signature rather than an opaque
import.
