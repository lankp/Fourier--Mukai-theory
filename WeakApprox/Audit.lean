/-
Copyright (c) 2026 Formalization of Lank--Pauwels.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import WeakApprox

/-!
# Axiom audit

Every declaration below must depend only on `propext`, `Classical.choice` and
`Quot.sound`.  Compiling this file prints the audit.
-/

@[expose] public section

namespace RelativeWeakApprox

#print axioms SetupMain.theorem_1_1
#print axioms SetupMain.theorem_1_1_forward
#print axioms SetupMain.eventuallyHomZero_G
#print axioms SetupMain.thick_G'
#print axioms theorem_1_1_of_setup
#print axioms satisfiesWA_of_setup
#print axioms lemma_4_3_2
#print axioms lemma_3_5
#print axioms isCompactAb_biprod
#print axioms isCompactAb_of_isCoproductCompact
#print axioms isCompactAb_leftAdjoint_obj'

end RelativeWeakApprox
