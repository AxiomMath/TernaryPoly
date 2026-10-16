module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.LeviReduction

@[expose] public section


/-! Ported from the Sol reference implementation. -/

open GeneralEisenstein Homogeneous Adelic Matrix

namespace TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

noncomputable section

def binaryLineLeviHom (R : Type) [CommRing R] : GeneralLinearGroup (Fin 2) R →* GeneralLinearGroup (Fin 3) R where
  toFun binary := lineLevi 1 binary
  map_one' := (lineLeviHom R).map_one
  map_mul' first second := by
    have identity := (lineLeviHom R).map_mul (1, first) (1, second)
    change lineLevi (1 * 1) (first * second) = lineLevi 1 first * lineLevi 1 second at identity
    simpa only [one_mul] using identity

def binaryArithmeticRationalLevi : binaryArithmeticLevel →* RationalGL3 :=
  (binaryLineLeviHom ℚ).comp
    ((GeneralLinearGroup.map (Int.castRingHom ℚ)).comp binaryArithmeticLevel.subtype)

theorem standardBadLine_inr_binary (element : binaryArithmeticLevel) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inr (1, element))).val =
      binaryArithmeticRationalLevi element := by
  rw [standardBadLineSemidirectEquiv_inr]
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (lineLevi 1 element.val) =
    lineLevi 1 (GeneralLinearGroup.map (Int.castRingHom ℚ) element.val)
  rw [map_lineLevi, map_one]

theorem binaryArithmeticRationalLevi_mem_level (element : binaryArithmeticLevel) :
    binaryArithmeticRationalLevi element ∈ rationalLevel := by
  rw [← standardBadLine_inr_binary]
  exact (standardBadLineSemidirectEquiv (SemidirectProduct.inr (1, element))).property.1

def binaryEdge (frame : GeneralLinearGroup (Fin 2) ℚ) : Edges :=
  QuotientGroup.mk (binaryLineLeviHom ℚ frame)

theorem binaryEdge_endpoint (frame : GeneralLinearGroup (Fin 2) ℚ) :
    endpoint .line (binaryEdge frame) = standardBadLine := by
  change (QuotientGroup.mk (lineLevi 1 frame) : Flags .line) = QuotientGroup.mk (1 : RationalGL3)
  apply QuotientGroup.eq.mpr
  change (lineLevi (1 : ℚˣ) frame)⁻¹ * 1 ∈ lineParabolic ℚ
  rw [mul_one]
  exact (lineParabolic ℚ).inv_mem (lineLevi_mem 1 frame)

theorem lineUnipotent_fixes_binaryEdge (frame : GeneralLinearGroup (Fin 2) ℚ)
    (first second : ℚ) : lineUnipotent first second • binaryEdge frame = binaryEdge frame := by
  change (QuotientGroup.mk (lineUnipotent first second * lineLevi 1 frame) : Edges) =
    QuotientGroup.mk (lineLevi 1 frame)
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  have identity := lineLevi_unipotent_conjugation (1 : ℚˣ) frame⁻¹ first second
  have conjugation : (lineLevi (1 : ℚˣ) frame)⁻¹ * lineUnipotent first second * lineLevi 1 frame =
      lineUnipotent (first * frame.val 0 0 + second * frame.val 1 0)
        (first * frame.val 0 1 + second * frame.val 1 1) := by
    simp only [lineLevi_inverse, inv_one, inv_inv, Units.val_one, one_mul] at identity ⊢
    exact identity
  rw [← mul_assoc, conjugation]
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem binaryEdge_radical_mem (frame : GeneralLinearGroup (Fin 2) ℚ)
    (radical : Multiplicative (ℤ × ℤ)) :
    (standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).val ∈
      fixedPointLevel rationalLevel (binaryEdge frame) := by
  refine ⟨(standardBadLineSemidirectEquiv (SemidirectProduct.inl radical)).property.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  rw [standardBadLineSemidirectEquiv_inl]
  change GeneralLinearGroup.map (Int.castRingHom ℚ)
    (lineUnipotent radical.toAdd.1 radical.toAdd.2) • binaryEdge frame = _
  rw [map_lineUnipotent]
  exact lineUnipotent_fixes_binaryEdge frame _ _

def binaryCuspLevel (frame : GeneralLinearGroup (Fin 2) ℚ) : Subgroup binaryArithmeticLevel :=
  (planeParabolic ℚ).comap
    ((MulAut.conj (binaryLineLeviHom ℚ frame)⁻¹).toMonoidHom.comp binaryArithmeticRationalLevi)

theorem binaryLevi_frame_conjugation (frame : GeneralLinearGroup (Fin 2) ℚ)
    (element : binaryArithmeticLevel) :
    (binaryLineLeviHom ℚ frame)⁻¹ * binaryArithmeticRationalLevi element * binaryLineLeviHom ℚ frame =
      binaryLineLeviHom ℚ (frame⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) element.val * frame) := by
  change (binaryLineLeviHom ℚ frame)⁻¹ *
    binaryLineLeviHom ℚ (GeneralLinearGroup.map (Int.castRingHom ℚ) element.val) * binaryLineLeviHom ℚ frame = _
  rw [← map_inv, ← map_mul, ← map_mul]

theorem mem_binaryCuspLevel_iff (frame : GeneralLinearGroup (Fin 2) ℚ)
    (element : binaryArithmeticLevel) :
    element ∈ binaryCuspLevel frame ↔
      (frame⁻¹ * GeneralLinearGroup.map (Int.castRingHom ℚ) element.val * frame).val 1 0 = 0 := by
  change (binaryLineLeviHom ℚ frame)⁻¹ * binaryArithmeticRationalLevi element *
    ((binaryLineLeviHom ℚ frame)⁻¹)⁻¹ ∈ planeParabolic ℚ ↔ _
  rw [inv_inv, binaryLevi_frame_conjugation]
  change InPlaneParabolic (lineLevi 1 _) ↔ _
  simp [InPlaneParabolic, lineLevi_val]

theorem binaryCusp_mem_edge (frame : GeneralLinearGroup (Fin 2) ℚ)
    (element : binaryCuspLevel frame) :
    binaryArithmeticRationalLevi element.val ∈ fixedPointLevel rationalLevel (binaryEdge frame) := by
  refine ⟨binaryArithmeticRationalLevi_mem_level element.val, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  change (QuotientGroup.mk (binaryArithmeticRationalLevi element.val * binaryLineLeviHom ℚ frame) : Edges) =
    QuotientGroup.mk (binaryLineLeviHom ℚ frame)
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  rw [← mul_assoc]
  constructor
  · have membership := element.property
    change (binaryLineLeviHom ℚ frame)⁻¹ * binaryArithmeticRationalLevi element.val *
      binaryLineLeviHom ℚ frame ∈ planeParabolic ℚ
    change (binaryLineLeviHom ℚ frame)⁻¹ * binaryArithmeticRationalLevi element.val *
      ((binaryLineLeviHom ℚ frame)⁻¹)⁻¹ ∈ planeParabolic ℚ at membership
    simpa only [inv_inv] using membership
  · rw [binaryLevi_frame_conjugation]
    exact lineLevi_mem 1 _

end

end TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
