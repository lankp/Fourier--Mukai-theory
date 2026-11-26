/- Copyright (c) 2026 Formalization of Lank--Pauwels. Released under Apache 2.0 license as described in the file LICENSE. -/
import WeakApprox.StatementAudit
import WeakApprox.CompactVanishing

/-!
# Literature audit: what is actually proved for schemes

## Verdict

The narrow claim behind the proposed refocus is **true with a stronger hypothesis
class than Noetherian**: all three requested inputs (weak approximability,
compact/perfect generation, and eventual positive Hom vanishing) are proved for
arbitrary quasi-compact quasi-separated (**qcqs**) schemes.  Separatedness is
not needed, and neither is finite Krull dimension.  A Noetherian scheme is qcqs
and every open subset is quasi-compact, so all supported versions below apply
to it without further topological hypotheses.

This does **not** imply that scheme GL26 is a published-library theorem.  GL26
Remark 2.6 additionally needs coherence and an intrinsic-subcategory theorem.
Its cited proofs of those inputs are preprints.  Nor does it supply any of the
relative-perfect/mate/base-change mathematics.  Counting only the three inputs
in the question gives **3/3 published scheme inputs**.  Counting the two extra
inputs explicitly used by Remark 2.6 leaves **2 further preprint-level inputs
outside that published Neeman theorem**.  The eventual-vanishing citation is
Stacks Tag 09MB, not Neeman's Theorem 3.2.

## (i)--(iii): exact statements and publication status

`Published` below means that the cited article is a peer-reviewed journal
article and the statement occurs with proof.  arXiv is used as the accessible
primary text, not as evidence of journal publication.

| input | exact scheme theorem | hypotheses | status |
|---|---|---|---|
| (i) weak approximation | Amnon Neeman, *Bounded t-structures on the category of perfect complexes*, Theorem 3.2(iv): `D_qc,Z(X)` is weakly approximable | `X` qcqs, `Z` closed with qc complement; take `Z=X` for `D_qc(X)` | **Published and proved**, Acta Math. 233 (2024), no. 2, 239--284, DOI `10.4310/ACTA.2024.v233.n2.a2`; final published arXiv text: https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 |
| (ii.a) compacts | Stacks Project, Tag 0AED (Lemma 75.16.3): an object of `D_QCoh,T(O_X)` is compact **iff** it is perfect as an object of `D(O_X)`.  The easy direction is Tag 09M8 (Proposition 75.16.1, perfect objects are compact); the converse uses the perfect compact generator of Tag 0AEC and the generator theorem Tag 09SR | `X` qcqs algebraic space over a scheme, `T` closed with quasi-compact complement; take `T = |X|` for all of `D_qc(X)` | **Published with proof**, https://stacks.math.columbia.edu/tag/0AED (with Tags 09M8, 0AEC, 09SR), which is the textbook form of Neeman, Theorem 3.2(i) |
| (ii.b) one generator | Stacks Project, Tag 0AEC (Lemma 75.15.6): there is a generator of `D_QCoh,T(O_X)` which is a perfect complex; it is compact by Tag 09M8 and it generates the compacts by Tag 09SR | qcqs; `T` closed with quasi-compact complement | **Published with proof**, https://stacks.math.columbia.edu/tag/0AEC (with Tags 09M8, 09SR), the textbook form of Neeman, Theorem 3.2(ii) |
| (iii) eventual Hom zero | Stacks Project, Tag 09MB (Lemma 75.17.2): for a perfect `K` there are integers `a ≤ b` with `Hom(K,L) = 0` for every `L ∈ D_QCoh` whose cohomology sheaves vanish in degrees `[a,b]`, and `Ext^n(K,L) = 0` for all but finitely many `n` when `L` is bounded.  With Tag 0AED (compacts are perfect) and Tag 0BCJ (perfect complexes have bounded cohomology), this gives `Hom(G,G'[n]) = 0` for `n ≫ 0` | qcqs; also gives the supported statement because compacts of `D_QCoh,T` are perfect on `X` (Tag 0AED) and the subcategory is full | **Published with proof**, https://stacks.math.columbia.edu/tag/09MB.  It is not accurate to attribute (iii) to Neeman's Theorem 3.2 alone |

For (iii), the proof is literally two lines.  Compacts `G,G'` are perfect by
Tag 0AED, and a perfect complex has bounded cohomology by Tag 0BCJ.  If
`H^i(G') = 0` for `i ∉ [c,d]`, then `H^i(G'[n]) = 0` for `i ∉ [c+n,d+n]`, so
Tag 09MB gives `Hom(G,G'[n]) = 0` as soon as `c+n > b` with `b` the upper end of
the window supplied by 09MB; Tag 09MB(2) gives the same conclusion directly
from boundedness of `G'`.  An independent amplitude proof is:
Stacks Tag 08DQ (Lemma 20.50.5) writes `Hom(G,M)` as
`H^0(X,G^∨ ⊗^L M)`, Tag 08D5 (Lemma 36.4.1(2)) gives uniform high-degree
vanishing for a qcqs pushforward, and `G^∨⊗G'` is bounded.  Primary sources:
https://stacks.math.columbia.edu/tag/08DQ and
https://stacks.math.columbia.edu/tag/08D5 .  Rouquier, Proposition 6.9, is a
second published amplitude statement (same URL as above).

Neeman's Remark 6.1 is also useful provenance: it identifies Theorem 3.2(i,ii)
as older results, whose textbook proofs are Stacks Tags 0AED and 0AEC, and
(iii,iv) as the new parts.  See https://arxiv.org/html/2202.08861v4#S6.Thmtheorem1 .

**Weak is not strong.**  Neeman's Remark 8.1 constructs supported examples
which are not approximable in the non-weak sense; Remark 8.2 recalls the older
result that `D_qc(X)` is approximable for a quasi-compact **separated** scheme.
That stronger theorem must not be substituted for Theorem 3.2(iv), which is
the qcqs weak statement and includes supports.  Source:
https://arxiv.org/html/2202.08861v4#S8 .

## What GL26 actually uses

The local source file was read directly.  Searches for the internal labels
`rmk:equivalences_induced`, `rem:rel_perfect_is_free`, `lem:equivalences_induced`,
`thm:fm_locus_weak_approx`, `lem:perf_vanishing`, and `lem:preferred_eq_class`
were cross-checked against the main text rather than inferring dependencies
from theorem names.

| GL26 location | use of (i)--(iii) and other inputs | scheme replacement / status |
|---|---|---|
| §2, Example 2.2 | compact = perfect and a classical compact generator; supported generation cites Rouquier | Stacks Tags 0AED and 0AEC, or Neeman 3.2(i,ii); published |
| Remark 2.6 (`rmk:equivalences_induced`) | assumes `D_qc(Y_i)` weakly approximable **and coherent**, then CHNS Theorem B gives equivalence on `D_qc ⇒ D^-_coh ⇒ D^b_coh ⇒ Perf`; the return implication uses a coproduct-preserving right adjoint and compacts | Neeman 3.2(iii,iv) gives the weak/preferred parts.  Coherence for qcqs coherent schemes (in particular Noetherian) is Neeman, arXiv:1806.06471v2, Example 5.4 (**preprint**, no journal reference on the abstract page): https://arxiv.org/html/1806.06471v2#S5.Thmtheorem4 .  CHNS Theorem B is Canonaco--Haesemeyer--Neeman--Stellari, arXiv:2402.04605v1 (**preprint**, no journal reference on the abstract page): https://arxiv.org/abs/2402.04605 .  The right-adjoint/compact input is Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown representability*, JAMS 9 (1996), Theorem 5.1 (published) |
| §10, Lemma 10.9 (`lem:equivalences_induced`) | alternative generation proof of `(D_qc ⇔ D^b_coh ⇔ Perf)` under relative-perfect hypotheses | weak approximability is expressly **not used**; Remark 2.6 itself says so.  Compact generation remains |
| §12, Definition 12.1 | defines the loci only | no approximability input |
| §12, Theorem 12.3 and Proposition 12.8 | chooses compact generators and identifies compacts with perfect complexes to detect relative perfection and openness | covered by Stacks Tags 0AED / 0AEC (or Neeman 3.2(i,ii)); no eventual-vanishing step |
| §12, Theorem 12.9 (`thm:fm_locus_weak_approx`) | through Remark 2.7 (`rem:rel_perfect_is_free`), an equivalence on any decorated category forces the kernel to be relatively perfect.  This puts `FM(E)` inside the open relative-perfect locus; Theorem 12.3 finishes | weak approximability **is used** (together with coherence and CHNS B via Remark 2.6).  Compact generation is also used.  There is no direct use of eventual Hom vanishing |
| Theorem 1.2(1) (`thm:fm_locus`) | is exactly Theorem 12.9(1) | therefore (i) and (ii) are genuinely used, indirectly as above; (iii) is not directly used |
| Appendix A, Lemmas `lem:BNP_weak_version_for_glueing` and `lem:etale_nbhd_preferred_class` | the gluing hypothesis includes eventual self-Hom vanishing, and the second proof asserts it for a perfect compact generator (with the paper's negative-shift convention) | covered by the same boundedness argument, but this is not a dependency of Theorem 1.2(1) |
| Appendix A, Lemma `lem:preferred_eq_class` | proves the standard `t`-structure is preferred first on the schematic locus, then by algebraic-space induction | Neeman 3.2(iii) is the scheme base case.  The whole induction disappears if only schemes are being formalized |

The paper's `cor:weak_approx_spaces` is in **LP**, not GL26.  LP Corollary 1.2
is the arXiv preprint https://arxiv.org/html/2610.22161v1#S1.Thmtheorem2 .  Its
proof uses algebraic-space induction from the schematic locus.  LP's lemmas
`lem:compact_ext_vanishing` and `lem:perf_vanishing` establish (iii) to feed
its Theorem 1.1.  For schemes, Neeman 3.2(iv) makes that entire gluing proof
unnecessary: **0 recollement induction steps and 0 uses of the LP eventual-
vanishing hypothesis are needed if the Acta theorem is imported directly**.
The pairwise statement (iii) is still available if a project instead wants to
rebuild weak approximation by gluing.

Coherence is a separate issue.  Neeman's preprint Example 5.4 proves it for a
qcqs coherent scheme by combining Theorem 3.2(iii,iv), Theorem 3.3's computation
of `T^-_c`, and the standard truncation `t`-structure.  Neeman's preprint
Remark 0.17 records the Noetherian consequence.  CHNS arXiv:2402.04605v1 is also
preprint status.  Thus "Neeman's *published* work covers weak approximability"
is correct, but "all of Remark 2.6 is published Neeman" would be false.

## Feasibility conclusion for the refocus

For the isolated target `D_qc(X) is weakly approximable` the scheme route is
strictly shorter in proof dependencies: cite one published theorem instead of
porting LP's induction over elementary distinguished squares.  Moreover the
class is qcqs, so choosing Noetherian schemes buys no additional weak-
approximability theorem.  The relevant formalization problem is therefore not
finding new mathematics for (i)--(iii); it is constructing enough of the
scheme category (`D_qc,Z`, compacts and perfects) to instantiate those truths.
The broader GL26 target still needs the independent preprint/categorical
inputs and its relative Fourier--Mukai geometry.

## Lean status of the declarations below

`CompactHomZeroAtTop` is a proposition template to be supplied when a future
`D_qc,Z` construction is instantiated.  The former templates `Neeman_3_2_i`,
`Neeman_3_2_ii` and `Neeman_3_2_iv` were deleted on `wave5/neeman-prune`
(26 November 2026): Neeman 2024, Theorem 3.2 is no longer an allowed input,
`Neeman_3_2_ii` was a false rendering (`IsGenerator` fails for `ℤ[0]`), and the
affine cases of (i), (ii) are proved in `Scheme/Neeman32Inputs.lean` (see
`results/NEEMAN_3_2.md`).  The only theorem proved here is the formal
specialization of pairwise compact vanishing to the self-vanishing appearing in
`SetupMainMinimal.theorem_1_1`.  The `#check`s verify the names used from the
current project; no claim about a Mathlib `IsPerfect` implementation is made.
-/

@[expose] public section
namespace RelativeFM

open RelativeWeakApprox

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.Triangulated

universe v u

section SchemeInputs

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **External literature hypothesis, Stacks Tag 09MB** (Lemma 75.17.2): for
every pair of compacts of `D_qc(X)` on a qcqs scheme, positive-shift Hom
eventually vanishes.  Compacts are perfect by Tag 0AED, perfect complexes have
bounded cohomology (Tag 0BCJ), and 09MB then bounds the Hom.  The same statement
for a full supported subcategory follows from the supported form of 0AED.
Sources: https://stacks.math.columbia.edu/tag/09MB,
https://stacks.math.columbia.edu/tag/0AED and
https://stacks.math.columbia.edu/tag/0BCJ .

For `X = Spec A` the vanishing half is **proved** here rather than assumed:
`perf_eventuallyHomZero` in `FourierMukai/Scheme/AffineMain.lean` proves the
ring analogue of 09MB for every commutative ring, with no input at all. -/
def CompactHomZeroAtTop : Prop :=
  ∀ G G' : C, IsCompactAb G → IsCompactAb G' → EventuallyHomZero G G'

omit [HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
/-- The self-vanishing required by `SetupMainMinimal.theorem_1_1` follows from
the published pairwise vanishing statement.  This is only the logical
specialization, not a formal proof of the geometric boundedness theorem. -/
theorem eventuallyHomZero_self_of_compactHomZeroAtTop
    (h : CompactHomZeroAtTop C) {G : C} (hG : IsCompactAb G) :
    EventuallyHomZero G G :=
  h G G hG hG

end SchemeInputs

#check WeakApproximationData
#check SatisfiesWA
#check IsCompactAb
#check IsGenerator
#check EventuallyHomZero
#check RelativeWeakApprox.SetupMainMinimal.theorem_1_1
#check RelativeWeakApprox.CompactHomZeroAtTop

end RelativeFM
