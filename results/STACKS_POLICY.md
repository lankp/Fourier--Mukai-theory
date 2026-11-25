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

## The library cannot be imported in this environment

`AxiomMath/Stacks` pins `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0` and ships no
build artifacts; this VM runs Lean 4.33.1 with a read-only prebuilt Mathlib and no
Lake.  So "assume" is realised as above — a tagged interface — rather than as an
import.  Reading the clone at `.scratch/stacks` for exact statements and names is
permitted and is how the interface was written.

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
