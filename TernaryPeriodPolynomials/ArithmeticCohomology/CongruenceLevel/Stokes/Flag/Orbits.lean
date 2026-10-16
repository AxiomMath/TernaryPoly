module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Plane.Orbits
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Faces.Flags

@[expose] public section


/-!
# The complete flags `F_g = g⁻¹ (ℚ e₁ ⊂ ⟨e₁, e₂⟩)` and their stabilizers in `Γ(6)`

Formalized by Claude Sonnet 5.5.

Every rational complete flag of the boundary labels is `F_g` for an integral `g ∈ SL₃(ℤ)` (`exists_flagOf`), and the stabilizer of `F_g` in `Γ(6)` is the flag group `gammaNBAt 6 g`
(`mem_stabilizer_flagOf_iff`).
-/

open CategoryTheory
open scoped MatrixGroups

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPoly.IntegralGL3Congruence
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryFullAction (lineAction planeAction subspaceAction vectorAction)

section Flags

theorem stdLine_lt_stdPlane : stdLine.val < stdPlane.val := by
  refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 (Submodule.subset_span (by simp))) ?_
  intro h
  have : e1 ∈ stdLine.val := by
    rw [h]
    exact Submodule.subset_span (by simp)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  have := congrFun hc 1
  simp [e0, e1] at this

theorem lineOf_lt_planeOf (g : SL(3, ℤ)) : (lineOf g).val < (planeOf g).val := by
  change (subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) stdLine.val) <
    (subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹) stdPlane.val)
  exact (subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ g⁻¹)).lt_iff_lt.2 stdLine_lt_stdPlane

/-- The complete flag `g⁻¹ (ℚ e₁ ⊂ ⟨e₁, e₂⟩)` of an integral change of basis. -/
def flagOf (g : SL(3, ℤ)) : Flag := ⟨(lineOf g, planeOf g), lineOf_lt_planeOf g⟩

theorem smul_flagOf (p : gammaN 6) (g : SL(3, ℤ)) : gammaSixEquiv p • flagOf g = flagOf (g * p.1⁻¹) := by
  apply Subtype.ext
  apply Prod.ext
  · exact smul_lineOf p g
  · exact smul_planeOf p g

theorem mem_stabilizer_flagOf_iff (p : gammaN 6) (g : SL(3, ℤ)) :
    gammaSixEquiv p ∈ MulAction.stabilizer Γ6 (flagOf g) ↔ p.1 ∈ gammaNBAt 6 g := by
  rw [MulAction.mem_stabilizer_iff, smul_flagOf]
  have hmem : g * p.1 * g⁻¹ ∈ gammaN 6 := by
    have := (gammaN_normal 6).conj_mem _ p.2 g
    simpa [mul_assoc] using this
  constructor
  · intro h
    have h1 : lineOf (g * p.1⁻¹) = lineOf g := congrArg (fun F : Flag => F.val.1) h
    have h2 : planeOf (g * p.1⁻¹) = planeOf g := congrArg (fun F : Flag => F.val.2) h
    rw [lineOf_eq_iff] at h1
    rw [planeOf_eq_iff] at h2
    have e : g * (g * p.1⁻¹)⁻¹ = g * p.1 * g⁻¹ := by group
    rw [e] at h1 h2
    exact ⟨hmem, h1.1, h1.2, h2.2⟩
  · intro h
    have h1 : lineOf (g * p.1⁻¹) = lineOf g := by
      rw [lineOf_eq_iff]
      have e : g * (g * p.1⁻¹)⁻¹ = g * p.1 * g⁻¹ := by group
      rw [e]
      exact ⟨h.2.1, h.2.2.1⟩
    have h2 : planeOf (g * p.1⁻¹) = planeOf g := by
      rw [planeOf_eq_iff]
      have e : g * (g * p.1⁻¹)⁻¹ = g * p.1 * g⁻¹ := by group
      rw [e]
      exact ⟨h.2.2.1, h.2.2.2⟩
    exact Subtype.ext (Prod.ext h1 h2)


theorem blockDiag_mem_planeBorel (B : SL(2, ℤ)) : blockDiag B ∈ planeBorel := by
  refine ⟨?_, ?_⟩ <;> simp [blockDiag]

theorem lineAction_inv_apply (g : GL (Fin 3) ℚ) (ℓ : Line) : lineAction g⁻¹ (lineAction g ℓ) = ℓ := by
  rw [← lineAction_mul, inv_mul_cancel, lineAction_one]

theorem lineAction_apply_inv (g : GL (Fin 3) ℚ) (ℓ : Line) : lineAction g (lineAction g⁻¹ ℓ) = ℓ := by
  rw [← lineAction_mul, mul_inv_cancel, lineAction_one]

theorem exists_line_in_stdPlane_normalize (ℓ' : Line) (hℓ' : ℓ'.val ≤ stdPlane.val) :
    ∃ q : SL(3, ℤ), q ∈ planeBorel ∧ lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q) ℓ' = stdLine := by
  have hpos : 0 < Module.finrank ℚ ℓ'.val := by rw [ℓ'.2.1]; exact Nat.one_pos
  obtain ⟨v, hvℓ, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Submodule.one_le_finrank_iff.1 hpos)
  have hspan : ℓ'.val = Submodule.span ℚ {v} := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · exact (Submodule.span_singleton_le_iff_mem _ _).2 hvℓ
    · rw [finrank_span_singleton hv0, ℓ'.2.1]
  have hv2 : v 2 = 0 := last_of_mem_stdSpan v (hℓ' hvℓ)
  obtain ⟨r, hprim, c, hc, hrc⟩ := exists_primitive_row v hv0
  have hr2 : r 2 = 0 := by
    have := hrc 2
    rw [hv2, mul_zero] at this
    exact_mod_cast this
  have hcop : IsCoprime (-(r 1)) (r 0) := by
    have h1 : Int.gcd (r 0) (r 1) = 1 := by
      have := hprim
      rw [hr2, Int.gcd_zero_right] at this
      simpa using this
    have h2 : IsCoprime (r 0) (r 1) := Int.isCoprime_iff_gcd_eq_one.2 h1
    exact (h2.symm.neg_left)
  obtain ⟨B, hB1, hB2⟩ := hcop.exists_SL2_row 1
  refine ⟨blockDiag B, blockDiag_mem_planeBorel B, ?_⟩
  apply Subtype.ext
  have hle : (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B)) ℓ').val ≤ stdLine.val := by
    rw [lineAction_val, hspan, Submodule.map_span, Set.image_singleton, Submodule.span_singleton_le_iff_mem]
    have hv : (vectorAction (Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B))).toLinearMap v =
        ((Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B) : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec v :=
      vectorAction_apply _ _
    rw [hv]
    have hq1 : (((Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B) : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec v) 1 = 0 := by
      rw [mulVec_mapGL, Fin.sum_univ_three]
      have e10 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 1 0) = -r 1 := hB1
      have e11 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 1 1) = r 0 := hB2
      have e12 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 1 2) = 0 := by simp [blockDiag]
      rw [e10, e11, e12]
      have := hrc 0
      have := hrc 1
      push_cast
      rw [hrc 0, hrc 1]
      ring
    have hq2 : (((Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B) : GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec v) 2 = 0 := by
      rw [mulVec_mapGL, Fin.sum_univ_three]
      have e20 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 2 0) = 0 := by simp [blockDiag]
      have e21 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 2 1) = 0 := by simp [blockDiag]
      have e22 : ((blockDiag B : Matrix (Fin 3) (Fin 3) ℤ) 2 2) = 1 := by simp [blockDiag]
      rw [e20, e21, e22, hv2]
      simp
    refine Submodule.mem_span_singleton.2 ⟨(((Matrix.SpecialLinearGroup.mapGL ℚ (blockDiag B) :
      GL (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ).mulVec v) 0, ?_⟩
    funext i
    fin_cases i
    · simp only [Pi.smul_apply, e0, Pi.single_apply, smul_eq_mul]
      simp
    · simp only [Pi.smul_apply, e0, Pi.single_apply, smul_eq_mul]
      erw [hq1]
      simp
    · simp only [Pi.smul_apply, e0, Pi.single_apply, smul_eq_mul]
      erw [hq2]
      simp
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [(lineAction _ ℓ').2.1, stdLine.2.1])


/-- **Every rational complete flag is `F_g` for an integral `g ∈ SL₃(ℤ)`.** -/
theorem exists_flagOf (F : Flag) : ∃ g : SL(3, ℤ), flagOf g = F := by
  obtain ⟨⟨ℓ, P⟩, hinc⟩ := F
  obtain ⟨h₂, hP⟩ := exists_planeOf P
  -- the image of `ℓ` under `h₂` lies in the standard plane
  have hℓP : ℓ.val < P.val := hinc
  have himg : (lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂) ℓ).val ≤ stdPlane.val := by
    have h1 : subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂) ℓ.val ≤
        subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂) P.val :=
      (subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂)).monotone hℓP.le
    have h2 : subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂) P.val = stdPlane.val := by
      rw [← hP]
      change subspaceAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂)
        (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂⁻¹) stdPlane).val = _
      change (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂)
        (planeAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂⁻¹) stdPlane)).val = _
      rw [← planeAction_mul, ← map_mul, mul_inv_cancel, map_one, planeAction_one]
    exact h2 ▸ h1
  obtain ⟨q, hq, hqℓ⟩ := exists_line_in_stdPlane_normalize _ himg
  refine ⟨q * h₂, ?_⟩
  have hqinv : q⁻¹ ∈ planeBorel := planeBorel.inv_mem hq
  apply Subtype.ext
  apply Prod.ext
  · change lineOf (q * h₂) = ℓ
    rw [lineOf, mul_inv_rev, map_mul, lineAction_mul]
    have : lineAction (Matrix.SpecialLinearGroup.mapGL ℚ q⁻¹) stdLine =
        lineAction (Matrix.SpecialLinearGroup.mapGL ℚ h₂) ℓ := by
      rw [← hqℓ, map_inv, lineAction_inv_apply]
    rw [this, map_inv, lineAction_inv_apply]
  · change planeOf (q * h₂) = P
    rw [planeOf, mul_inv_rev, map_mul, planeAction_mul]
    have : planeAction (Matrix.SpecialLinearGroup.mapGL ℚ q⁻¹) stdPlane = stdPlane :=
      (planeAction_stdPlane_eq_iff q⁻¹).2 hqinv
    rw [this]
    exact hP

end Flags

end TernaryPeriodPolynomials.Argument.GammaNStokes
