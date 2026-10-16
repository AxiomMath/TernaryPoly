module

public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerEdgePrimitives
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.Binary.Cusps

@[expose] public section


/-!
# Complete flags over the standard bad line, and their stabilizers

Every complete flag whose line endpoint is `standardBadLine` is `binaryEdge frame` for a frame of
`GL₂(ℚ)` (`exists_binaryEdge`), and an element `x = n · inr (u, b)` of the standard bad-line
stabilizer fixes `binaryEdge frame` exactly when its binary part `b` lies in the cusp subgroup
`binaryCuspLevel frame` (`ambient_mem_edge_iff`). Together with the mixed-class exactness of
`MixedSubgroup` this describes the edge stabilizers inside the split extension
`N ⋊ (ℤˣ × binaryArithmeticLevel)`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein Homogeneous Adelic Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers

namespace TernaryPeriodPolynomials.Argument.FacePairingFull

/-- The scalar-twisted binary Levi has the same complete flag as the untwisted one. -/
theorem mk_lineLevi_scalar (d : ℚˣ) (frame : GeneralLinearGroup (Fin 2) ℚ) :
    (QuotientGroup.mk (lineLevi d frame) : Edges) = binaryEdge frame := by
  change (QuotientGroup.mk (lineLevi d frame) : Edges) = QuotientGroup.mk (lineLevi 1 frame)
  apply QuotientGroup.eq.mpr
  have product : (lineLevi d frame)⁻¹ * lineLevi 1 frame = lineLevi d⁻¹ 1 := by
    have key : (((d : ℚˣ), frame)⁻¹ * ((1 : ℚˣ), frame) :
        ℚˣ × GeneralLinearGroup (Fin 2) ℚ) = (d⁻¹, 1) := by
      ext <;> simp
    have h := congrArg (lineLeviHom ℚ) key
    simp only [map_mul, map_inv] at h
    exact h
  rw [product]
  refine ⟨?_, lineLevi_mem _ _⟩
  change (lineLevi d⁻¹ 1).val 2 0 = 0 ∧ (lineLevi d⁻¹ 1).val 2 1 = 0
  rw [lineLevi_val]
  exact ⟨rfl, rfl⟩

/-- **Edges over the standard bad line are binary edges.** -/
theorem exists_binaryEdge (edge : Edges) (endpointEq : endpoint .line edge = standardBadLine) :
    ∃ frame : GeneralLinearGroup (Fin 2) ℚ, edge = binaryEdge frame := by
  induction edge using QuotientGroup.induction_on with
  | H g =>
    have hmem : g ∈ lineParabolic ℚ := by
      have h := QuotientGroup.eq.mp endpointEq
      have h' : g⁻¹ ∈ parabolic .line := by simpa using h
      have h'' : g ∈ parabolic .line := by simpa using (parabolic .line).inv_mem h'
      exact h''
    let element : lineParabolic ℚ := ⟨g, hmem⟩
    have decomposition := lineParabolic_radical_levi element
    have hg : lineUnipotent (lineRadicalCoordinates element).1 (lineRadicalCoordinates element).2 *
        lineLevi (lineScalar element) (lineBinary element) = g := decomposition
    refine ⟨lineBinary element, ?_⟩
    rw [← hg]
    change lineUnipotent (lineRadicalCoordinates element).1 (lineRadicalCoordinates element).2 •
        (QuotientGroup.mk (lineLevi (lineScalar element) (lineBinary element)) : Edges) = _
    rw [mk_lineLevi_scalar]
    exact lineUnipotent_fixes_binaryEdge _ _ _

/-- A Levi element fixes `binaryEdge frame` exactly when its binary block fixes the cusp of `frame`. -/
theorem lineLevi_smul_binaryEdge_iff (frame : GeneralLinearGroup (Fin 2) ℚ) (d : ℚˣ)
    (B : GeneralLinearGroup (Fin 2) ℚ) :
    lineLevi d B • binaryEdge frame = binaryEdge frame ↔
      (frame⁻¹ * B * frame).val 1 0 = 0 := by
  change (QuotientGroup.mk (lineLevi d B * lineLevi 1 frame) : Edges) =
    QuotientGroup.mk (lineLevi 1 frame) ↔ _
  rw [eq_comm, QuotientGroup.eq]
  have conj : (lineLevi 1 frame)⁻¹ * (lineLevi d B * lineLevi 1 frame) =
      lineLevi d (frame⁻¹ * B * frame) := by
    have key : (((1 : ℚˣ), frame)⁻¹ * ((d, B) * ((1 : ℚˣ), frame)) :
        ℚˣ × GeneralLinearGroup (Fin 2) ℚ) = (d, frame⁻¹ * B * frame) := by
      ext <;> simp [mul_assoc]
    have h := congrArg (lineLeviHom ℚ) key
    simp only [map_mul, map_inv] at h
    exact h
  rw [conj]
  constructor
  · intro h
    have h2 : (lineLevi d (frame⁻¹ * B * frame)).val 2 1 = 0 := h.1.2
    rw [lineLevi_val] at h2
    simpa using h2
  · intro h
    refine ⟨⟨?_, ?_⟩, lineLevi_mem _ _⟩
    · change (lineLevi d (frame⁻¹ * B * frame)).val 2 0 = 0
      rw [lineLevi_val]
      rfl
    · change (lineLevi d (frame⁻¹ * B * frame)).val 2 1 = 0
      rw [lineLevi_val]
      simpa using h

/-- The ambient matrix of `inr (u, b)` in the standard bad-line stabilizer. -/
theorem standardBadLine_inr_ambient (u : ℤˣ) (b : binaryArithmeticLevel) :
    standardBadLineAmbientHom (SemidirectProduct.inr (u, b)) =
      lineLevi (Units.map (Int.castRingHom ℚ).toMonoidHom u)
        (GeneralLinearGroup.map (Int.castRingHom ℚ) b.val) := by
  change (standardBadLineSemidirectEquiv (SemidirectProduct.inr (u, b))).val = _
  rw [standardBadLineSemidirectEquiv_inr]
  change GeneralLinearGroup.map (Int.castRingHom ℚ) (lineLevi u b.val) = _
  rw [map_lineLevi]

/-- **Edge stabilizers inside the Levi.** The Levi element `(u, b)` of the standard bad-line
stabilizer fixes `binaryEdge frame` if and only if `b` lies in the cusp subgroup of `frame`. -/
theorem ambient_inr_mem_edge_iff (frame : GeneralLinearGroup (Fin 2) ℚ) (u : ℤˣ)
    (b : binaryArithmeticLevel) :
    standardBadLineAmbientHom (SemidirectProduct.inr (u, b)) ∈
        fixedPointLevel rationalLevel (binaryEdge frame) ↔ b ∈ binaryCuspLevel frame := by
  rw [standardBadLine_inr_ambient, mem_binaryCuspLevel_iff]
  constructor
  · intro h
    exact (lineLevi_smul_binaryEdge_iff frame _ _).mp (MulAction.mem_stabilizer_iff.mp h.2)
  · intro h
    refine ⟨?_, MulAction.mem_stabilizer_iff.mpr
      ((lineLevi_smul_binaryEdge_iff frame _ _).mpr h)⟩
    rw [← standardBadLine_inr_ambient]
    exact (standardBadLineSemidirectEquiv (SemidirectProduct.inr (u, b))).property.1

end TernaryPeriodPolynomials.Argument.FacePairingFull
