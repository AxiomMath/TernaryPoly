module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Face.CuspIso
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.LevelOneCusps
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Parabolic.H1Dictionary
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Arithmetic.StabilizerEdge

@[expose] public section


/-!
# The cusp subgroups of the good line are the cusp stabilizers of `GL₂(ℤ)`

Every complete flag over the good line `ℚe₃` is `rationalGoodLine • binaryEdge A` for a frame
`A ∈ GL₂(ℚ)` and the Levi `GL₂(ℤ)` of the good line acts on it through the reversed block
`J l J`; hence the cusp subgroup `faceCusp e` of the flag is the stabilizer in `GL₂(ℤ)` of the cusp of
the frame `J A` (`faceCusp_goodLine`). Consequently a class of `H¹(GL₂(ℤ), H¹(N, Sym^n))`
vanishing on all cusp stabilizers is mixed cuspidal (`mem_faceCuspidal_goodLine_of`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Matrix GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (goodLineSemidirectEquiv goodLineSplitting RadicalLattice arithmeticLevi rationalGoodLine
    goodLineRadicalInclusion
    rationalGoodLine_inverse goodLineLeviSection)
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelThree
  (swapQ swapQ_inv)
open TernaryPeriodPolynomials.Argument.FacePairingFull.Parabolic
open TernaryPeriodPolynomials.SphericalDetection.Helpers
  (lowerRadicalLatticeRep lowerRadicalLattice lowerRadicalH1Levi goodLineCoefficientRep
    goodLineSplitH1Action splitRadicalH1Action splitRadicalH1Action_apply lowerRadicalH1Coordinate
    splitRadicalCocycleAction arithmeticBinaryRep lowerRadicalH1Coordinate_equivariant)

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Face

theorem goodLine_levi_val (l : GeneralLinearGroup (Fin 2) ℤ) :
    (goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val = arithmeticLevi l := by
  change (goodLineRadicalInclusion 1 * goodLineSplitting l).val = _
  rw [map_one, one_mul]
  rfl

/-- Conjugating the Levi of the good line by the long Weyl element reverses the binary block. -/
theorem weyl_conj_arithmeticLevi (l : GeneralLinearGroup (Fin 2) ℤ) :
    rationalGoodLine⁻¹ * arithmeticLevi l * rationalGoodLine =
      lineLevi (1 : ℚˣ) (swapQ * GeneralLinearGroup.map (Int.castRingHom ℚ) l * swapQ) := by
  rw [rationalGoodLine_inverse]
  apply Units.ext
  rw [lineLevi_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [arithmeticLevi, planeLevi, planeBlock, rationalGoodLine, swapQ,
      GeneralLinearGroup.map, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.vecMul, dotProduct]

/-- **The cusp subgroup of a complete flag over the good line is a cusp stabilizer of `GL₂(ℤ)`.** -/
theorem faceCusp_goodLine (e : Edges) (he : endpoint .line e = goodLineFlag) :
    ∃ A : GeneralLinearGroup (Fin 2) ℚ,
      faceCusp goodLineSplitting.conjAct goodLineFlag goodLineSemidirectEquivFixed e = cuspStab A := by
  have he' : endpoint .line (rationalGoodLine⁻¹ • e) = standardBadLine := by
    rw [endpoint_smul, he]
    change rationalGoodLine⁻¹ • (QuotientGroup.mk rationalGoodLine : Flags .line) =
      QuotientGroup.mk 1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
  obtain ⟨frame, hframe⟩ := exists_binaryEdge _ he'
  have heq : e = rationalGoodLine • binaryEdge frame := by
    rw [← hframe, smul_inv_smul]
  refine ⟨swapQ * frame, ?_⟩
  ext l
  rw [mem_cuspStab_iff]
  change (goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val ∈
    fixedPointLevel rationalLevel e ↔ _
  rw [goodLine_levi_val]
  constructor
  · intro h
    have hfix : arithmeticLevi l • e = e := MulAction.mem_stabilizer_iff.mp h.2
    rw [heq, ← mul_smul, show arithmeticLevi l * rationalGoodLine =
      rationalGoodLine * (rationalGoodLine⁻¹ * arithmeticLevi l * rationalGoodLine) by group,
      mul_smul, weyl_conj_arithmeticLevi] at hfix
    have := (lineLevi_smul_binaryEdge_iff frame 1 _).mp (smul_left_cancel _ hfix)
    simpa [swapQ_inv, mul_assoc] using this
  · intro h
    refine ⟨?_, MulAction.mem_stabilizer_iff.mpr ?_⟩
    · rw [← goodLine_levi_val]
      exact (goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).property.1
    · rw [heq, ← mul_smul, show arithmeticLevi l * rationalGoodLine =
        rationalGoodLine * (rationalGoodLine⁻¹ * arithmeticLevi l * rationalGoodLine) by group,
        mul_smul, weyl_conj_arithmeticLevi]
      congr 1
      apply (lineLevi_smul_binaryEdge_iff frame 1 _).mpr
      simpa [swapQ_inv, mul_assoc] using h

/-- The radical representation of the good line, on the face presentation. -/
abbrev glRad (n : ℕ) :=
  (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
    goodLineSemidirectEquivFixed).comp SemidirectProduct.inl

/-- The radical module of the good line, on the face presentation. -/
abbrev GLModule (n : ℕ) := CrossedH1 (glRad n)

/-- The Levi action on the good-line radical cohomology. -/
abbrev glAction (n : ℕ) : Representation ℂ (GeneralLinearGroup (Fin 2) ℤ) (GLModule n) :=
  leviCrossedH1Representation goodLineSplitting.conjAct
    (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed)

theorem faceRep_goodLine_radical (n : ℕ) :
    (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed).comp SemidirectProduct.inl =
      (lowerRadicalLatticeRep n).ρ := by
  apply MonoidHom.ext
  intro r
  change rationalCoefficientComponent n trivialCharacter
    (goodLineSemidirectEquivFixed (SemidirectProduct.inl r)).val =
    rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice r)
  rw [goodLineSemidirectEquiv_inl]
  rfl

theorem faceRep_goodLine_levi (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ) :
    faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag goodLineSemidirectEquivFixed
        (SemidirectProduct.inr l) =
      (goodLineCoefficientRep n).ρ (goodLineSplitting l) := by
  change rationalCoefficientComponent n trivialCharacter
    (goodLineSemidirectEquivFixed (SemidirectProduct.inr l)).val = _
  rw [goodLine_levi_val]
  rfl

/-- Crossed `H¹` of the radical versus Mathlib `H¹` of the lattice representation. -/
def glToH1 (n : ℕ) : GLModule n ≃ₗ[ℂ] groupCohomology.H1 (lowerRadicalLatticeRep n) :=
  (crossedH1RepresentationEqEquiv _ _ (faceRep_goodLine_radical n)).trans
    (h1EquivCrossed (lowerRadicalLatticeRep n))

theorem glAction_cocycle (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ)
    (φ : crossedCocycles ((faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed).comp SemidirectProduct.inl)) :
    cocycleOfCrossed (lowerRadicalLatticeRep n)
        (crossedRepresentationEqEquiv _ _ (faceRep_goodLine_radical n)
          (leviCrossedAction goodLineSplitting.conjAct
            (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
              goodLineSemidirectEquivFixed) l φ)) =
      splitRadicalCocycleAction goodLineSplitting (goodLineCoefficientRep n) l
        (cocycleOfCrossed (lowerRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_goodLine_radical n) φ)) := by
  apply Subtype.ext
  funext r
  change (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed (SemidirectProduct.inr l)) (φ.val (goodLineSplitting.conjAct l⁻¹ r)) =
    (goodLineCoefficientRep n).ρ (goodLineSplitting l) (φ.val (goodLineSplitting.conjAct l⁻¹ r))
  rw [faceRep_goodLine_levi]
  rfl

theorem glToH1_equivariant (n : ℕ) (l : GeneralLinearGroup (Fin 2) ℤ) (c : GLModule n) :
    glToH1 n (glAction n l c) = lowerRadicalH1Levi n l (glToH1 n c) := by
  obtain ⟨φ, rfl⟩ := (crossedBoundaries (glRad n)).mkQ_surjective c
  have h2 : glAction n l ((crossedBoundaries (glRad n)).mkQ φ) =
      (crossedBoundaries (glRad n)).mkQ (leviCrossedAction goodLineSplitting.conjAct
        (faceRep goodLineSplitting.conjAct n trivialCharacter goodLineFlag
          goodLineSemidirectEquivFixed) l φ) := leviCrossedH1Representation_mk _ _ l φ
  have h3 : ∀ ψ, glToH1 n ((crossedBoundaries (glRad n)).mkQ ψ) =
      groupCohomology.H1π (lowerRadicalLatticeRep n)
        (cocycleOfCrossed (lowerRadicalLatticeRep n)
          (crossedRepresentationEqEquiv _ _ (faceRep_goodLine_radical n) ψ)) := fun ψ => rfl
  refine ((congrArg (glToH1 n) h2).trans (h3 _)).trans ?_
  refine (congrArg (groupCohomology.H1π (lowerRadicalLatticeRep n)) (glAction_cocycle n l φ)).trans ?_
  refine (splitRadicalH1Action_apply goodLineSplitting (goodLineCoefficientRep n) l _).symm.trans ?_
  rw [goodLineSplitH1Action]
  rfl

variable (n : ℕ) (positive : 0 < n)

/-- Kostant isomorphism `H¹(N, Sym^n) ≅ Sym^{n+1}` for the good line. -/
def glTheta : GLModule n ≃ₗ[ℂ] Binary.HomogeneousPoly (n + 1) :=
  (glToH1 n).trans (lowerRadicalH1Coordinate n positive)

theorem glTheta_equivariant (l : GeneralLinearGroup (Fin 2) ℤ) (c : GLModule n) :
    glTheta n positive (glAction n l c) =
      (arithmeticBinaryRep (n + 1) 0).ρ l (glTheta n positive c) := by
  change lowerRadicalH1Coordinate n positive (glToH1 n (glAction n l c)) = _
  rw [glToH1_equivariant, lowerRadicalH1Coordinate_equivariant]
  rfl

theorem glTransport_eq :
    coefficientTransportRepresentation (glAction n) (glTheta n positive) =
      (arithmeticBinaryRep (n + 1) 0).ρ := by
  apply MonoidHom.ext
  intro l
  apply LinearMap.ext
  intro v
  rw [coefficientTransportRepresentation_apply, glTheta_equivariant, LinearEquiv.apply_symm_apply]
  rfl

/-- Change of coefficients `H¹(L, H¹(N, E)) ≅ H¹(L, Sym^{n+1})` for the good line. -/
def glPsi : CrossedH1 (glAction n) ≃ₗ[ℂ] CrossedH1 (arithmeticBinaryRep (n + 1) 0).ρ :=
  (crossedH1CoefficientEquiv (glAction n) (glTheta n positive)).trans
    (crossedH1RepresentationEqEquiv _ _ (glTransport_eq n positive))

theorem glPsi_mk (x : crossedCocycles (glAction n)) :
    ∃ y : crossedCocycles (arithmeticBinaryRep (n + 1) 0).ρ,
      (∀ l, y.val l = glTheta n positive (x.val l)) ∧
        glPsi n positive ((crossedBoundaries (glAction n)).mkQ x) =
          (crossedBoundaries (arithmeticBinaryRep (n + 1) 0).ρ).mkQ y :=
  ⟨crossedRepresentationEqEquiv _ _ (glTransport_eq n positive)
    (crossedCoefficientEquiv (glAction n) (glTheta n positive) x), fun _ => rfl, rfl⟩

/-- Cuspidal at all frames implies mixed cuspidal at the good line. -/
theorem mem_faceCuspidal_goodLine_of
    (m : CrossedH1 (glAction n))
    (h : ∀ A : GeneralLinearGroup (Fin 2) ℚ,
      crossedPullbackH1 (cuspStab A).subtype (glAction n) m = 0) :
    m ∈ (FaceCuspidal goodLineSplitting.conjAct n trivialCharacter goodLineFlag
      goodLineSemidirectEquivFixed : Submodule ℂ (CrossedH1 (glAction n))) := by
  refine (mem_faceCuspidal_iff goodLineSplitting.conjAct n trivialCharacter goodLineFlag
    goodLineSemidirectEquivFixed m).mpr fun e => ?_
  have cuspFrame := faceCusp_goodLine e.val e.property
  obtain ⟨A, hA⟩ := cuspFrame
  have hA' := h A
  rw [← hA] at hA'
  exact hA'

end TernaryPeriodPolynomials.Argument.FacePairingFull.Face
