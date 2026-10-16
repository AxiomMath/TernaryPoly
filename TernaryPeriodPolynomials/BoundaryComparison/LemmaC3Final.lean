module

public import TernaryPeriodPolynomials.BoundaryComparison.MixedCuspidal.Transfer
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.InnerDecomposition

@[expose] public section


/-!
# Lemma C.3, last sentence: the inner plane classes are spanned by the transfers of the `Γ(N)` seeds

Paper: Lemma C.3 (`ar:lem:seed`), last
sentence: "Eichler--Shimura theory therefore shows that the holomorphic and
antiholomorphic seeds span `𝒞_P(E)` after including all plane cusps and finite reflections", with
`𝒞_P(E)` the direct sum over the faces of type `P` of the mixed cuspidal groups and
"rationally conjugate the finitely many other plane cusps to `P`".

The faces of type `P` of the paper's level group `Γ = {g ∈ GL₃(ℤ) | e₃*g ≡ e₃* mod 3}` are the
two `Γ`-orbits of rational planes, good and bad (`GoodFlag`).  The face library packages the inner
classes of the plane side (`InnerBoundary`) as the direct sum of the locally inner classes at one good
and one bad plane (`innerClassesEquivLocal`, from `innerBoundary_iff_locallyInner_reps` /
`innerBoundary_iff_locallyInner_cusps`).  Combining with `MixedCuspidalTransfer`:

* `lemma_C3_final_sentence`: for **any** integral representatives `hg`, `hb` of a good and a bad plane,
  the image of the inner classes under `innerClassesEquivLocal` is exactly the product of the
  **transfers (corestrictions) of the spans of the holomorphic and antiholomorphic seeds of `Γ(N)`** at
  `hg` and `hb` (`N ≥ 3`, `3 ∣ N`: the neat principal congruence subgroups of level divisible by three of
  Appendix C);
* `lemma_C3_final_sentence_reference`: the same at the reference planes `⟨e₃, e₂⟩` (`wGood`) and
  `⟨e₁, e₂⟩` (`1`).

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.LemmaC3Final

open GeneralEisenstein Matrix
open TernaryPeriodPolynomials.Argument
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

/-- The direct sum decomposition of the inner plane classes at a good and a bad plane. -/
def innerPlaneEquiv (n : ℕ) (hg hb : SL(3, ℤ)) (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg))
    (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb)) :=
  FacePairingFull.Face.innerClassesEquivLocal n (SeedC3S4c.planeFlagAt hg)
    (SeedC3S4c.planeFlagAt hb) hgood hbad

/-- **Lemma C.3, last sentence.**  For `N ≥ 3` with `3 ∣ N` and integral representatives `hg`, `hb` of
a good and a bad rational plane, the inner classes of the plane side are the direct sum
(`innerClassesEquivLocal`) of the locally inner classes at the two planes, and each summand is exactly the
transfer of the span of the holomorphic and antiholomorphic seeds of `Γ(N)` at that plane: (A) every
inner class has both components of this form and (B) every pair of such transfers occurs. -/
theorem lemma_C3_final_sentence (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (hg hb : SL(3, ℤ)) (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt hg))
    (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt hb)) (n : ℕ) :
    (∀ c : FacePairingFull.innerClasses n .plane,
      ∃ yg ∈ SeedC3S4c.faceSeedSpan N hg n, ∃ yb ∈ SeedC3S4c.faceSeedSpan N hb n,
        ((innerPlaneEquiv n hg hb hgood hbad c).1 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt hg))
            (rationalCoefficientComponent n trivialCharacter)) =
          SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg ∧
        ((innerPlaneEquiv n hg hb hgood hbad c).2 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt hb))
            (rationalCoefficientComponent n trivialCharacter)) =
          SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb) ∧
    (∀ yg ∈ SeedC3S4c.faceSeedSpan N hg n, ∀ yb ∈ SeedC3S4c.faceSeedSpan N hb n,
      ∃ c : FacePairingFull.innerClasses n .plane,
        ((innerPlaneEquiv n hg hb hgood hbad c).1 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt hg))
            (rationalCoefficientComponent n trivialCharacter)) =
          SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg ∧
        ((innerPlaneEquiv n hg hb hgood hbad c).2 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt hb))
            (rationalCoefficientComponent n trivialCharacter)) =
          SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb) := by
  constructor
  · intro c
    have hmp1 := (MixedCuspidalTransfer.locally_inner_iff_transfer_of_seed_span N h3 hN
      hg n trivialCharacter _).mp (innerPlaneEquiv n hg hb hgood hbad c).1.property
    have hmp2 := (MixedCuspidalTransfer.locally_inner_iff_transfer_of_seed_span N h3 hN
      hb n trivialCharacter _).mp (innerPlaneEquiv n hg hb hgood hbad c).2.property
    exact ⟨hmp1.choose, hmp1.choose_spec.1, hmp2.choose, hmp2.choose_spec.1,
      hmp1.choose_spec.2.symm, hmp2.choose_spec.2.symm⟩
  · intro yg hyg yb hyb
    have h1 := (MixedCuspidalTransfer.locally_inner_iff_transfer_of_seed_span N h3 hN hg n
      trivialCharacter (SeedC3S4c.planeTransfer N h3 hN hg n trivialCharacter yg)).mpr
      ⟨yg, hyg, rfl⟩
    have h2 := (MixedCuspidalTransfer.locally_inner_iff_transfer_of_seed_span N h3 hN hb n
      trivialCharacter (SeedC3S4c.planeTransfer N h3 hN hb n trivialCharacter yb)).mpr
      ⟨yb, hyb, rfl⟩
    have key := LinearEquiv.apply_symm_apply (innerPlaneEquiv n hg hb hgood hbad) (⟨_, h1⟩, ⟨_, h2⟩)
    exact ⟨_, congrArg (fun p => Subtype.val p.1) key,
      congrArg (fun p => Subtype.val p.2) key⟩

/-- **The same at the reference planes**: the good plane `⟨e₃, e₂⟩` (`wGood`) and the bad plane
`⟨e₁, e₂⟩` (`1`). -/
theorem lemma_C3_final_sentence_reference (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) :
    ∃ (hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt SeedC3S4c.wGood))
      (hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt 1)),
      (∀ c : FacePairingFull.innerClasses n .plane,
        ∃ yg ∈ SeedC3S4c.faceSeedSpan N SeedC3S4c.wGood n, ∃ yb ∈ SeedC3S4c.faceSeedSpan N 1 n,
          ((innerPlaneEquiv n SeedC3S4c.wGood 1 hgood hbad c).1 :
            Homogeneous.H2 (fixedPointLevel rationalLevel
              (SeedC3S4c.planeFlagAt SeedC3S4c.wGood))
              (rationalCoefficientComponent n trivialCharacter)) =
            SeedC3S4c.planeTransfer N h3 hN SeedC3S4c.wGood n trivialCharacter yg ∧
          ((innerPlaneEquiv n SeedC3S4c.wGood 1 hgood hbad c).2 :
            Homogeneous.H2 (fixedPointLevel rationalLevel (SeedC3S4c.planeFlagAt 1))
              (rationalCoefficientComponent n trivialCharacter)) =
            SeedC3S4c.planeTransfer N h3 hN 1 n trivialCharacter yb) := by
  have hgood : GoodFlag .plane (SeedC3S4c.planeFlagAt SeedC3S4c.wGood) := by
    rw [SeedC3S4c.planeFlagAt_wGood]; exact FacePairingFull.Face.goodPlaneFlag_good
  have hbad : ¬ GoodFlag .plane (SeedC3S4c.planeFlagAt 1) := by
    rw [SeedC3S4c.planeFlagAt_one]; exact FacePairingFull.Face.badPlaneFlag_not_good
  exact ⟨hgood, hbad, (lemma_C3_final_sentence N h3 hN _ _ hgood hbad n).1⟩

end TernaryPeriodPolynomials.Argument.Statements.LemmaC3Final
