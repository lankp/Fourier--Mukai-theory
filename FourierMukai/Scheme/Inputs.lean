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
Bondal--Van den Bergh, not Neeman.

## (i)--(iii): exact statements and publication status

`Published` below means that the cited article is a peer-reviewed journal
article and the statement occurs with proof.  arXiv is used as the accessible
primary text, not as evidence of journal publication.

| input | exact scheme theorem | hypotheses | status |
|---|---|---|---|
| (i) weak approximation | Amnon Neeman, *Bounded t-structures on the category of perfect complexes*, Theorem 3.2(iv): `D_qc,Z(X)` is weakly approximable | `X` qcqs, `Z` closed with qc complement; take `Z=X` for `D_qc(X)` | **Published and proved**, Acta Math. 233 (2024), no. 2, 239--284, DOI `10.4310/ACTA.2024.v233.n2.a2`; final published arXiv text: https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 |
| (ii.a) compacts | Neeman, Theorem 3.2(i): compacts of `D_qc,Z(X)` are perfect complexes on `X` with cohomology supported on `Z`; independently Bondal--Van den Bergh, Theorem 3.1.1(1) for `Z=X` | qcqs in both | **Published and proved**, Neeman as above; A. Bondal and M. Van den Bergh, *Generators and representability of functors in commutative and noncommutative geometry*, Mosc. Math. J. 3 (2003), no. 1, 1--36, 258, https://arxiv.org/pdf/math/0204218 |
| (ii.b) one generator | Neeman, Theorem 3.2(ii); independently Bondal--Van den Bergh, Theorem 3.1.1(2); for supports, Rouquier, Theorem 6.8 | qcqs; for supports, qc complement | **Published and proved**, same sources; R. Rouquier, *Dimensions of triangulated categories*, J. K-Theory 1 (2008), 193--256, https://www.math.ucla.edu/~rouquier/papers/dimension.pdf |
| (iii) eventual Hom zero | Bondal--Van den Bergh, Lemma 3.3.8 says `RHom(E,F)` is bounded for perfect `E`; Theorem 3.1.1 says every compact is perfect.  Hence, for compacts `G,G'`, `Hom(G,G'[n])=0` for `n≫0` | qcqs; also gives the supported statement because compacts there are perfect on `X` and the subcategory is full | **Published ingredients with an immediate proof**, same 2003 article.  It is not accurate to attribute (iii) to Neeman's Theorem 3.2 alone |

For (iii), the proof is literally two lines.  Compacts `G,G'` are perfect by
Theorem 3.1.1.  Perfect complexes are bounded, and Lemma 3.3.8 makes the
derived global Hom complex bounded; shifting its bounded nonzero cohomology
window beyond zero gives the cutoff.  An independent amplitude proof is:
Stacks Tag 08DQ (Lemma 20.50.5) writes `Hom(G,M)` as
`H^0(X,G^∨ ⊗^L M)`, Tag 08D5 (Lemma 36.4.1(2)) gives uniform high-degree
vanishing for a qcqs pushforward, and `G^∨⊗G'` is bounded.  Primary sources:
https://stacks.math.columbia.edu/tag/08DQ and
https://stacks.math.columbia.edu/tag/08D5 .  Rouquier, Proposition 6.9, is a
second published amplitude statement (same URL as above).

Neeman's Remark 6.1 is also useful provenance: it identifies Theorem 3.2(i,ii)
as older results (Bondal--Van den Bergh and Rouquier), and (iii,iv) as the new
parts.  See https://arxiv.org/html/2202.08861v4#S6.Thmtheorem1 .

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
| §2, Example 2.2 | compact = perfect and a classical compact generator; supported generation cites Rouquier | Bondal--Van den Bergh 3.1.1, Rouquier 6.8, or Neeman 3.2(i,ii); published |
| Remark 2.6 (`rmk:equivalences_induced`) | assumes `D_qc(Y_i)` weakly approximable **and coherent**, then CHNS Theorem B gives equivalence on `D_qc ⇒ D^-_coh ⇒ D^b_coh ⇒ Perf`; the return implication uses a coproduct-preserving right adjoint and compacts | Neeman 3.2(iii,iv) gives the weak/preferred parts.  Coherence for qcqs coherent schemes (in particular Noetherian) is Neeman, arXiv:1806.06471v2, Example 5.4 (**preprint**, no journal reference on the abstract page): https://arxiv.org/html/1806.06471v2#S5.Thmtheorem4 .  CHNS Theorem B is Canonaco--Haesemeyer--Neeman--Stellari, arXiv:2402.04605v1 (**preprint**, no journal reference on the abstract page): https://arxiv.org/abs/2402.04605 .  The right-adjoint/compact input is Neeman, *The Grothendieck duality theorem via Bousfield's techniques and Brown representability*, JAMS 9 (1996), Theorem 5.1 (published) |
| §10, Lemma 10.9 (`lem:equivalences_induced`) | alternative generation proof of `(D_qc ⇔ D^b_coh ⇔ Perf)` under relative-perfect hypotheses | weak approximability is expressly **not used**; Remark 2.6 itself says so.  Compact generation remains |
| §12, Definition 12.1 | defines the loci only | no approximability input |
| §12, Theorem 12.3 and Proposition 12.8 | chooses compact generators and identifies compacts with perfect complexes to detect relative perfection and openness | covered by Bondal--Van den Bergh 3.1.1 / Neeman 3.2(i,ii); no eventual-vanishing step |
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

`Neeman_3_2_iv`, `Neeman_3_2_ii`, `Neeman_3_2_i`, and
`CompactHomZeroAtTop` are proposition templates to be supplied when a future
`D_qc,Z` construction is instantiated.  They do not pretend that Lean already
has that geometric construction.  The only theorem proved here is the formal
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

/-- **External literature hypothesis, Neeman 2024, Theorem 3.2(iv).**
When `C` is `D_qc,Z(X)` for a qcqs scheme and a closed subset with
quasi-compact complement, this is its weak approximability.  The geometric
construction is missing here; this `Prop` is to be assumed from the cited
paper, not proved by this file.  Source:
https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 . -/
def Neeman_3_2_iv : Prop := SatisfiesWA C

/-- **External literature hypothesis, Neeman 2024, Theorem 3.2(ii)** (also
Bondal--Van den Bergh 2003, Theorem 3.1.1(2), and Rouquier 2008, Theorem 6.8
for supports).  For a qcqs scheme, `D_qc,Z(X)` has a single compact generator.
Source: https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 . -/
def Neeman_3_2_ii : Prop :=
  ∃ G : C, IsCompactAb G ∧ IsGenerator G

/-- **External literature hypothesis, Neeman 2024, Theorem 3.2(i)** (also
Bondal--Van den Bergh 2003, Theorem 3.1.1(1)).  Instantiate `PerfectSupported`
by the perfect complexes on `X` whose cohomology is supported on `Z`; perfection
is deliberately a parameter rather than a fictitious Mathlib declaration.
Source: https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 . -/
def Neeman_3_2_i (PerfectSupported : C → Prop) : Prop :=
  ∀ P : C, IsCompactAb P ↔ PerfectSupported P

/-- **External literature hypothesis, Bondal--Van den Bergh 2003**,
Theorem 3.1.1 and Lemma 3.3.8: for every pair of compacts of `D_qc(X)` on a
qcqs scheme, positive-shift Hom eventually vanishes.  The same statement for a
full supported subcategory follows using Neeman 3.2(i).  Sources:
https://arxiv.org/pdf/math/0204218 and
https://arxiv.org/html/2202.08861v4#S3.Thmtheorem2 . -/
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

/-- **External preprint hypothesis, Neeman arXiv:1806.06471v2, Example 5.4.**
For a qcqs coherent scheme (in particular a Noetherian scheme), `D_qc,Z(X)` is
weakly approximable and coherent.  `CoherentTriangulated` is a parameter because
this project has not formalized that separate notion.  This is a preprint input,
distinct from the published Acta theorem.  Source:
https://arxiv.org/html/1806.06471v2#S5.Thmtheorem4 . -/
def Neeman_coherent_example_5_4 (CoherentTriangulated : Prop) : Prop :=
  Neeman_3_2_iv C ∧ CoherentTriangulated

end SchemeInputs

#check WeakApproximationData
#check SatisfiesWA
#check IsCompactAb
#check IsGenerator
#check EventuallyHomZero
#check RelativeWeakApprox.SetupMainMinimal.theorem_1_1
#check RelativeWeakApprox.CompactHomZeroAtTop


end RelativeFM
