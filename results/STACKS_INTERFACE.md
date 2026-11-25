# Assuming AxiomMath/Stacks: what that can and cannot mean here

**Decision (from the person).**  The development may now assume the
[AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) formalization of the Stacks
Project, in addition to Neeman's Acta paper.  Target assumption set: **Stacks +
Neeman, nothing else**, for GL26 with an affine base.

## The environment constraint

`AxiomMath/Stacks` **cannot be imported in this VM**, and this is not a matter of
effort:

* the clone at `.scratch/stacks` pins `leanprover/lean4:v4.35.0` and Mathlib
  `v4.35.0`;
* this VM has Lean **4.33.1** and a read-only prebuilt Mathlib at 4.33.1, with no
  Lake build;
* the clone has no `.lake/build` artifacts.

Porting it to 4.33.1 is the person-months job estimated in
[`STACKS_PORTABILITY.md`](STACKS_PORTABILITY.md).

## What we do instead

Assume Stacks the way any large library is assumed when it cannot be linked: as a
**tagged interface**.  Each statement we take from Stacks becomes one `Prop`-valued
field of a structure, carrying its tag number and the exact statement, in the style
of [`../FourierMukai/Scheme/Inputs.lean`](../FourierMukai/Scheme/Inputs.lean).  The
development is then conditional on that structure, and the assumption set is a
finite, auditable list of tags rather than an opaque import.

This is strictly more informative than an import would be: it says exactly which
part of Stacks each step uses.

## What the clone tells us the interface should say

Reading the clone's source (permitted — it is a reference) gives the exact form of
the statements, which matters because a tag can be instantiated in several ways.

* **Tag 0A6R** is realised there as
  `Stacks.LocalCohomology.CechFormula.localCohomologyCechIso`, the *natural*
  isomorphism of functors on `D(A)`

  ```
  RΓ_Z  ≅  C(f) ⊗^L_A (-)
  ```

  with the tag attribute attached to that half of the statement, and the module
  notes say explicitly which half is not proved there (naturality in one direction,
  and the identification at arbitrary objects of `D(A)` rather than at a single
  module).  This is the form our recount needs: it converts the missing
  `jStarAdj` into the tensor–Hom adjunction for the single object `C(f)`.
* The clone has a substantial `DerivedTensor/` development (bifunctor, associativity,
  unit comparisons, K-flatness), i.e. the derived tensor we lack is present there, so
  the interface can legitimately take the derived tensor and its unit as given.
* It also contains `Perfect/`, `Spaces/Perfect/`, `Duality/`, and
  `Quasicoherent/` trees, so tags 0AED, 09M1, 09M8, 09MB, 0BCJ, 08CM, 0E56, 0A8A,
  04LX, 08JB, 0A6H, 0D0S are all available as interface fields if we want them — even
  though we have proved most of them here already.

## Consequence for the assumption ledger

For every tag the tree currently cites, there is now a choice: **prove it here** (as
we do for 01LA, 01IE, 01HV, 066S, 066T, 07LT, 09M1, 09M8, 09MB, 09SR, 0AED, 0BCJ) or
**assume it from Stacks**.  The rule we adopt: keep our own proof where it exists and
is cheap to maintain, and assume from Stacks only where we have no proof — currently
the derived tensor with its tensor–Hom adjunction (0A6R and the K-flat/K-projective
material it rests on).  Our own proofs are not weaker than an assumption; they are
strictly better, and dropping them would make the development depend on more.
