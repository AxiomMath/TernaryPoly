module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.Uniform
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.BadLineEdges
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerSplitting

@[expose] public section


/-!
# The good line `ℚe₃`: stabilizer `3ℤ² ⋊ GL₂(ℤ)` and its cusp subgroups

The stabilizer of the line `ℚe₃` (the image of the standard line `ℚe₁` under the long Weyl
element `rationalGoodLine`) in the arithmetic level is the split extension `3ℤ² ⋊ GL₂(ℤ)`
(`SphericalDetection.goodLineSemidirectEquiv`). Its radical fixes every complete flag over the
line (it is the Weyl conjugate of a subgroup of the radical of the standard line, which fixes the
flags `binaryEdge frame`), so `Face/Uniform` applies (`goodLine_locallyInner_iff`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSemidirectEquiv goodLineSplitting RadicalLattice lowerRadicalLattice
    goodLineRadicalInclusion rationalGoodLine rationalGoodLine_inverse)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- The good line `ℚe₃`. -/
def goodLineFlag : Flags .line := QuotientGroup.mk rationalGoodLine

/-- The split presentation of the stabilizer of the good line. -/
def goodLineSemidirectEquivFixed :
    RadicalLattice ⋊[goodLineSplitting.conjAct] GeneralLinearGroup (Fin 2) ℤ ≃*
      ↥(fixedPointLevel rationalLevel goodLineFlag) :=
  goodLineSemidirectEquiv

theorem goodLineSemidirectEquiv_inl (radical : RadicalLattice) :
    (goodLineSemidirectEquivFixed (SemidirectProduct.inl radical)).val =
      lowerPlaneUnipotent (3 * (radical.toAdd.1 : ℚ)) (3 * (radical.toAdd.2 : ℚ)) := by
  change (goodLineRadicalInclusion radical * goodLineSplitting 1).val = _
  rw [map_one, mul_one]
  rfl

theorem lowerPlaneUnipotent_eq_conj (x y : ℚ) :
    lowerPlaneUnipotent x y = rationalGoodLine * lineUnipotent y x * rationalGoodLine⁻¹ := by
  rw [rationalGoodLine_inverse]
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rationalGoodLine, lowerPlaneUnipotent, lineUnipotent, upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_three]

/-- **The radical of the good line fixes every complete flag over it.** -/
theorem goodLine_radical_fixes (radical : RadicalLattice) (e : Edges)
    (he : endpoint .line e = goodLineFlag) :
    (goodLineSemidirectEquivFixed (SemidirectProduct.inl radical)).val • e = e := by
  have he' : endpoint .line (rationalGoodLine⁻¹ • e) = standardBadLine := by
    rw [endpoint_smul, he]
    change rationalGoodLine⁻¹ • (QuotientGroup.mk rationalGoodLine : Flags .line) =
      QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  obtain ⟨frame, hframe⟩ := exists_binaryEdge _ he'
  have heq : e = rationalGoodLine • binaryEdge frame := by
    rw [← hframe, smul_inv_smul]
  rw [goodLineSemidirectEquiv_inl, lowerPlaneUnipotent_eq_conj, heq, mul_smul, mul_smul,
    inv_smul_smul, lineUnipotent_fixes_binaryEdge]

/-- The Levi `GL₂(ℤ)` of the good line embeds in `GL₂(ℤ) × ℤˣ`. -/
def goodLineLeviEmbedding : GeneralLinearGroup (Fin 2) ℤ →* GeneralLinearGroup (Fin 2) ℤ × ℤˣ :=
  (MonoidHom.id _).prod 1

theorem goodLineLeviEmbedding_injective : Function.Injective goodLineLeviEmbedding :=
  fun _ _ h => congrArg Prod.fst h

/-- **Good line: locally inner iff mixed cuspidal**, for every degree. -/
theorem goodLine_locallyInner_iff (degree : ℕ) (character : RankOneCharacter)
    (coordinate : H2 (fixedPointLevel rationalLevel goodLineFlag)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character .line goodLineFlag ↔
      ∃ radicalZero : faceH2Equiv goodLineSplitting.conjAct degree character goodLineFlag
          goodLineSemidirectEquivFixed coordinate ∈
          (radicalRestrictionH2 goodLineSplitting.conjAct (faceRep goodLineSplitting.conjAct
            degree character goodLineFlag goodLineSemidirectEquivFixed)).ker,
        ∀ e : Edges, endpoint .line e = goodLineFlag →
          crossedPullbackH1 (faceCusp goodLineSplitting.conjAct goodLineFlag
              goodLineSemidirectEquivFixed e).subtype
            (leviCrossedH1Representation goodLineSplitting.conjAct
              (faceRep goodLineSplitting.conjAct degree character goodLineFlag
                goodLineSemidirectEquivFixed))
            (radicalKernelMixedMap goodLineSplitting.conjAct
              (faceRep goodLineSplitting.conjAct degree character goodLineFlag
                goodLineSemidirectEquivFixed)
              ⟨faceH2Equiv goodLineSplitting.conjAct degree character goodLineFlag
                goodLineSemidirectEquivFixed coordinate, radicalZero⟩) = 0 :=
  face_locallyInner_iff_uniform goodLineSplitting.conjAct degree character goodLineFlag
    goodLineSemidirectEquivFixed (fun radical e he => goodLine_radical_fixes radical e he)
    goodLineLeviEmbedding goodLineLeviEmbedding_injective coordinate

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
