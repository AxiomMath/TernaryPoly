module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.LineLevelDescent
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.FaceOrbits
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.InnerDecomposition
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.ReferencePlanes

@[expose] public section


/-!
# Lemma C.3, last sentence, for the line side: inner line classes are the transfers of the `Γ(N)` mixed cuspidal groups

Formalized by Claude Sonnet 5.5.
Paper: Appendix C.

The faces of type `Q` of the level group are the two orbits of rational lines, good and bad.  The face library packages the inner classes of the
line side as the direct sum of the locally inner classes at one good and one bad line (`innerClassesEquivLocal`).  Combining with
`LineLevelDescent.locallyInnerClasses_lineFlag_eq_transfer`:

* `lemma_C3_final_sentence_line`: for **any** integral representatives `hg`, `hb` of a good and a bad line, the image of the inner line
  classes under `innerClassesEquivLocal` is exactly the product of the **transfers (corestrictions) of `lineFaceCuspidalInH2`**, the image of
  the literal mixed cuspidal groups `𝒞_{Q'}(E)` of `Γ(N)`, at `hg` and `hb` (`N ≥ 3`, `3 ∣ N`);
* `lineFlagAt_one`, `lineFlagAt_wGood`, `lemma_C3_final_sentence_line_reference`: the same at the reference lines `ℚ e₁` (bad, `1`) and
  `ℚ e₃` (good, `wGood`).
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFacesFull

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces

theorem lineFlagAt_one : lineFlagAt 1 = standardBadLine := by
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (1 : SL(3, ℤ))⁻¹) : Flags .line) =
    QuotientGroup.mk 1
  simp

theorem lineFlagAt_wGood : lineFlagAt wGood = FacePairingFull.Face.goodLineFlag := by
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ wGood⁻¹) : Flags .line) =
    QuotientGroup.mk TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine
  rw [wGood_inv]
  apply QuotientGroup.eq.mpr
  rw [← map_inv, wGood_inv]
  refine ⟨?_, ?_⟩
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    change ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 1 0 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 0 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 1 1 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 1 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 1 2 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 2 0 = 0
    simp [wGood, TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three]
    change ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 0 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 1 0 +
      ((wGood : Matrix (Fin 3) (Fin 3) ℤ) 2 2 : ℚ) *
        (TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine : RationalGL3).val 2 0 = 0
    simp [wGood, TernaryPeriodPolynomials.SphericalDetection.Helpers.rationalGoodLine]

open TernaryPeriodPolynomials.Argument

/-- The direct sum decomposition of the inner line classes at a good and a bad line. -/
def innerLineEquiv (n : ℕ) (hg hb : SL(3, ℤ)) (hgood : GoodFlag .line (lineFlagAt hg))
    (hbad : ¬ GoodFlag .line (lineFlagAt hb)) :=
  FacePairingFull.Face.innerClassesEquivLocal n (lineFlagAt hg) (lineFlagAt hb) hgood hbad

/-- **Line version of the last sentence of Lemma C.3.**  For `N ≥ 3` with `3 ∣ N` and integral representatives `hg`, `hb` of a good and a
bad rational line, the inner classes of the line side are the direct sum (`innerClassesEquivLocal`) of the locally inner classes at the two
lines, and each summand is exactly the transfer (corestriction) of the image `lineFaceCuspidalInH2` of the literal mixed cuspidal group
`𝒞_{Q'}(E)` of `Γ(N)` at that line: (A) every inner class has both components of this form and (B) every pair of such transfers occurs. -/
theorem lemma_C3_final_sentence_line (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N)
    (hg hb : SL(3, ℤ)) (hgood : GoodFlag .line (lineFlagAt hg))
    (hbad : ¬ GoodFlag .line (lineFlagAt hb)) (n : ℕ) :
    (∀ c : FacePairingFull.innerClasses n .line,
      ∃ yg ∈ lineFaceCuspidalInH2 N hg n, ∃ yb ∈ lineFaceCuspidalInH2 N hb n,
        ((innerLineEquiv n hg hb hgood hbad c).1 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt hg))
            (rationalCoefficientComponent n trivialCharacter)) =
          lineTransfer N h3 hg n trivialCharacter hN yg ∧
        ((innerLineEquiv n hg hb hgood hbad c).2 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt hb))
            (rationalCoefficientComponent n trivialCharacter)) =
          lineTransfer N h3 hb n trivialCharacter hN yb) ∧
    (∀ yg ∈ lineFaceCuspidalInH2 N hg n, ∀ yb ∈ lineFaceCuspidalInH2 N hb n,
      ∃ c : FacePairingFull.innerClasses n .line,
        ((innerLineEquiv n hg hb hgood hbad c).1 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt hg))
            (rationalCoefficientComponent n trivialCharacter)) =
          lineTransfer N h3 hg n trivialCharacter hN yg ∧
        ((innerLineEquiv n hg hb hgood hbad c).2 :
          Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt hb))
            (rationalCoefficientComponent n trivialCharacter)) =
          lineTransfer N h3 hb n trivialCharacter hN yb) := by
  constructor
  · intro c
    have hmp1 := (locallyInnerClasses_lineFlag_eq_transfer N h3 hg n trivialCharacter hN _).mp
      (innerLineEquiv n hg hb hgood hbad c).1.property
    have hmp2 := (locallyInnerClasses_lineFlag_eq_transfer N h3 hb n trivialCharacter hN _).mp
      (innerLineEquiv n hg hb hgood hbad c).2.property
    exact ⟨hmp1.choose, hmp1.choose_spec.1, hmp2.choose, hmp2.choose_spec.1,
      hmp1.choose_spec.2.symm, hmp2.choose_spec.2.symm⟩
  · intro yg hyg yb hyb
    have h1 := (locallyInnerClasses_lineFlag_eq_transfer N h3 hg n trivialCharacter hN
      (lineTransfer N h3 hg n trivialCharacter hN yg)).mpr ⟨yg, hyg, rfl⟩
    have h2 := (locallyInnerClasses_lineFlag_eq_transfer N h3 hb n trivialCharacter hN
      (lineTransfer N h3 hb n trivialCharacter hN yb)).mpr ⟨yb, hyb, rfl⟩
    have key := LinearEquiv.apply_symm_apply (innerLineEquiv n hg hb hgood hbad) (⟨_, h1⟩, ⟨_, h2⟩)
    exact ⟨_, congrArg (fun p => Subtype.val p.1) key, congrArg (fun p => Subtype.val p.2) key⟩

/-- **The same at the reference lines**: the good line `ℚe₃` (`wGood`) and the bad line `ℚe₁` (`1`). -/
theorem lemma_C3_final_sentence_line_reference (N : ℕ) [NeZero N] (h3 : 3 ∣ N) (hN : 3 ≤ N) (n : ℕ) :
    ∃ (hgood : GoodFlag .line (lineFlagAt wGood)) (hbad : ¬ GoodFlag .line (lineFlagAt 1)),
      ∀ c : FacePairingFull.innerClasses n .line,
        ∃ yg ∈ lineFaceCuspidalInH2 N wGood n, ∃ yb ∈ lineFaceCuspidalInH2 N 1 n,
          ((innerLineEquiv n wGood 1 hgood hbad c).1 :
            Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt wGood))
              (rationalCoefficientComponent n trivialCharacter)) =
            lineTransfer N h3 wGood n trivialCharacter hN yg ∧
          ((innerLineEquiv n wGood 1 hgood hbad c).2 :
            Homogeneous.H2 (fixedPointLevel rationalLevel (lineFlagAt 1))
              (rationalCoefficientComponent n trivialCharacter)) =
            lineTransfer N h3 1 n trivialCharacter hN yb := by
  have hgood : GoodFlag .line (lineFlagAt wGood) := by
    rw [lineFlagAt_wGood]; exact FacePairingFull.Face.goodLineFlag_good
  have hbad : ¬ GoodFlag .line (lineFlagAt 1) := by
    rw [lineFlagAt_one]; exact FacePairingFull.Face.standardBadLine_not_good
  exact ⟨hgood, hbad, (lemma_C3_final_sentence_line N h3 hN _ _ hgood hbad n).1⟩

end TernaryPeriodPolynomials.Argument.GammaNFacesFull
