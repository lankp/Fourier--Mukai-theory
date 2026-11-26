/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import Spaces

/-!
# Statement check for the AxiomMath-based libraries

The pinned statements of `Spaces` (and later `SpacesVerified`): results in the papers'
hypotheses whose Stacks inputs are theorems of AxiomMath/Stacks.  Checked by
`scripts/check_statements.sh --spaces` against `results/statement-baseline-spaces.txt`;
it needs `lake build Spaces` (AxiomMath's definitions), so it is separate from the
default check.
-/

@[expose] public section
#check @RelativeFM.Spaces.Stacks.theorem_1_1
#check @RelativeFM.Spaces.Stacks.lemma_2_4
#check @RelativeFM.Spaces.Stacks.lemma_2_5
#check @RelativeFM.Spaces.Stacks.tag09SRPaper
#check @RelativeFM.Spaces.Stacks.tag09SN
#check @RelativeFM.Spaces.Stacks.isCompactObject_iff_isCompactAb
#check @RelativeFM.Spaces.Stacks.isWeakTriangulatedGenerator_singleton_iff
#print axioms RelativeFM.Spaces.Stacks.theorem_1_1
#print axioms RelativeFM.Spaces.Stacks.lemma_2_4
#print axioms RelativeFM.Spaces.Stacks.lemma_2_5
#print axioms RelativeFM.Spaces.Stacks.tag09SRPaper
#print axioms RelativeFM.Spaces.Stacks.tag09SN
#print axioms RelativeFM.Spaces.Stacks.isCompactObject_iff_isCompactAb
#print axioms RelativeFM.Spaces.Stacks.isWeakTriangulatedGenerator_singleton_iff
