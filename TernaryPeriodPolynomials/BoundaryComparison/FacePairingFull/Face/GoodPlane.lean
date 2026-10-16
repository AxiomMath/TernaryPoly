module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.BadLine
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Flags

@[expose] public section


/-!
# The good plane: the involution image of the standard bad line

The involution `φ` of the level exchanges the standard bad line with the dual plane
`dualFlag standardBadLine = ⟨e₃, e₂⟩` (the good plane), mapping the stabilizer of the line
isomorphically onto the stabilizer of the plane and the radical to the radical. Transporting the
split presentation of the line stabilizer along `φ` gives the split presentation of the good plane
stabilizer `ℤ² ⋊ (ℤˣ × binaryArithmeticLevel)`, with the same Levi (so the same embedding into
`GL₂(ℤ) × ℤˣ`), and the radical again fixes every complete flag over the plane. `Face/Uniform`
therefore applies, with no computation in the coefficients.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

/-- The good plane `⟨e₃, e₂⟩ = dualFlag standardBadLine`. -/
def goodPlaneFlag : Flags .plane := dualFlag standardBadLine

/-- The involution maps the stabilizer of the standard line onto that of the good plane. -/
def dualStabilizerEquiv :
    ↥(fixedPointLevel rationalLevel standardBadLine) ≃*
      ↥(fixedPointLevel rationalLevel goodPlaneFlag) where
  toFun g := ⟨dualInvolution g.val, dualInvolution_mem_rationalLevel g.property.1,
    MulAction.mem_stabilizer_iff.mpr (by
      show dualInvolution g.val • dualFlag standardBadLine = dualFlag standardBadLine
      rw [← dualFlag_smul, MulAction.mem_stabilizer_iff.mp g.property.2])⟩
  invFun g := ⟨dualInvolution g.val, dualInvolution_mem_rationalLevel g.property.1,
    MulAction.mem_stabilizer_iff.mpr (by
      have h := congrArg dualPlaneFlag (MulAction.mem_stabilizer_iff.mp g.property.2)
      have e : dualPlaneFlag goodPlaneFlag = standardBadLine := dualPlaneFlag_dualFlag _
      rw [dualPlaneFlag_smul, e] at h
      exact h)⟩
  left_inv g := Subtype.ext (dualInvolution_involutive g.val)
  right_inv g := Subtype.ext (dualInvolution_involutive g.val)
  map_mul' g h := Subtype.ext (map_mul dualInvolution g.val h.val)

/-- The split presentation of the stabilizer of the good plane. -/
def goodPlaneSemidirectEquiv :
    BadLineSemidirect ≃* ↥(fixedPointLevel rationalLevel goodPlaneFlag) :=
  standardBadLineSemidirectEquiv.trans dualStabilizerEquiv

theorem goodPlaneSemidirectEquiv_val (x : BadLineSemidirect) :
    (goodPlaneSemidirectEquiv x).val = dualInvolution (standardBadLineSemidirectEquiv x).val :=
  rfl

/-- **The radical of the good plane fixes every complete flag over it.** -/
theorem goodPlane_radical_fixes (radical : Multiplicative (ℤ × ℤ)) (e : Edges)
    (he : endpoint .plane e = goodPlaneFlag) :
    (goodPlaneSemidirectEquiv (SemidirectProduct.inl radical)).val • e = e := by
  have he' : endpoint .line (dualEdge e) = standardBadLine := by
    have e : dualPlaneFlag goodPlaneFlag = standardBadLine := dualPlaneFlag_dualFlag _
    rw [endpoint_line_dualEdge, he, e]
  have hfix := badLine_radical_fixes radical (dualEdge e) he'
  have h := congrArg dualEdge hfix
  rw [dualEdge_smul, dualEdge_dualEdge] at h
  rw [goodPlaneSemidirectEquiv_val]
  exact h

/-- **Good plane: locally inner iff mixed cuspidal**, for every degree. -/
theorem goodPlane_locallyInner_iff (degree : ℕ) (character : RankOneCharacter)
    (coordinate : H2 (fixedPointLevel rationalLevel goodPlaneFlag)
      (rationalCoefficientComponent degree character)) :
    coordinate ∈ locallyInnerClasses degree character .plane goodPlaneFlag ↔
      ∃ radicalZero : faceH2Equiv integralBadLineSplitting.conjAct degree character
          goodPlaneFlag goodPlaneSemidirectEquiv coordinate ∈
          (radicalRestrictionH2 integralBadLineSplitting.conjAct
            (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag
              goodPlaneSemidirectEquiv)).ker,
        ∀ e : Edges, endpoint .plane e = goodPlaneFlag →
          crossedPullbackH1 (faceCusp integralBadLineSplitting.conjAct goodPlaneFlag
              goodPlaneSemidirectEquiv e).subtype
            (leviCrossedH1Representation integralBadLineSplitting.conjAct
              (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag
                goodPlaneSemidirectEquiv))
            (radicalKernelMixedMap integralBadLineSplitting.conjAct
              (faceRep integralBadLineSplitting.conjAct degree character goodPlaneFlag
                goodPlaneSemidirectEquiv)
              ⟨faceH2Equiv integralBadLineSplitting.conjAct degree character goodPlaneFlag
                goodPlaneSemidirectEquiv coordinate, radicalZero⟩) = 0 :=
  face_locallyInner_iff_uniform integralBadLineSplitting.conjAct degree character goodPlaneFlag
    goodPlaneSemidirectEquiv (fun radical e he => goodPlane_radical_fixes radical e he)
    badLineLeviEmbedding badLineLeviEmbedding_injective coordinate

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
