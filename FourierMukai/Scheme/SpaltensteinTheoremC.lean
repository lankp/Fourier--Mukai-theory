import FourierMukai.Scheme.SpaltensteinCanonicalTruncation
import FourierMukai.Scheme.SpaltensteinSequentialComparisons

/-!
# Spaltenstein's Theorem C interface

Combines the canonical-truncation construction with the two sequential-colimit
comparison proofs.
-/

@[expose] public section
namespace RelativeFM.Spaltenstein

open CategoryTheory CategoryTheory.Limits CochainComplex

universe v u
noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- All three fields of the reduced Spaltenstein Theorem C interface, for an
arbitrary abelian category.  The structure itself carries the exact-colimit
hypotheses where they are used. -/
noncomputable def theoremCInput : TheoremCInput C :=
  theoremCInputOfCanonicalTruncation canonicalTruncation

#print axioms RelativeFM.Spaltenstein.theoremCInput

end
end RelativeFM.Spaltenstein
