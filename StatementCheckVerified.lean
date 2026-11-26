/-
Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE.
-/
import SpacesVerified

/-!
# Statement check for `SpacesVerified`

The pinned statements of `SpacesVerified`: the tagged AxiomMath inputs of
`Spaces/AxiomMathInputs.lean`, proved by the AxiomMath theorems they name, and the
unconditional consequences.  Checked by `scripts/check_statements.sh --verified` against
`results/statement-baseline-verified.txt`; it needs `lake build SpacesVerified` (the full
AxiomMath build), so it is separate from the `--spaces` check.
-/

@[expose] public section
#check @RelativeFM.SpacesVerified.tag06UQ
#check @RelativeFM.SpacesVerified.tag08F4
#check @RelativeFM.SpacesVerified.tag08F5
#check @RelativeFM.SpacesVerified.tag08FA
#check @RelativeFM.SpacesVerified.Dqc_isTriangulated
#check @RelativeFM.SpacesVerified.tag06LT
#check @RelativeFM.SpacesVerified.isQuasiCompactOfIsIso
#check @RelativeFM.SpacesVerified.universallyClosedOfIsIso
#check @RelativeFM.SpacesVerified.isFlatId
#check @RelativeFM.SpacesVerified.affineQuasiSeparated
#check @RelativeFM.SpacesVerified.setup_hypotheses_satisfiable_unconditional
#print axioms RelativeFM.SpacesVerified.tag06UQ
#print axioms RelativeFM.SpacesVerified.tag08F4
#print axioms RelativeFM.SpacesVerified.tag08F5
#print axioms RelativeFM.SpacesVerified.tag08FA
#print axioms RelativeFM.SpacesVerified.Dqc_isTriangulated
#print axioms RelativeFM.SpacesVerified.tag06LT
#print axioms RelativeFM.SpacesVerified.isQuasiCompactOfIsIso
#print axioms RelativeFM.SpacesVerified.universallyClosedOfIsIso
#print axioms RelativeFM.SpacesVerified.isFlatId
#print axioms RelativeFM.SpacesVerified.affineQuasiSeparated
#print axioms RelativeFM.SpacesVerified.setup_hypotheses_satisfiable_unconditional
