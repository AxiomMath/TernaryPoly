module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.CuspRestriction
public import TernaryPeriodPolynomials.EisensteinSeries.Class.ConstantTerm

@[expose] public section


/-!
# R2: plane flags versus cosets `Γ_P \ Γ`, and the orbit relation by cusp (`N ≥ 3`)

Formalized by Claude Sonnet 5.5.

* `planeFlagAt_eq_iff`: `planeFlagAt h = planeFlagAt h' ↔ h h'⁻¹ ∈ P(ℚ) ∩ SL₃(ℤ)` (`planeBorel`).
* `cosetFlag : Γ_P\Γ(N) → Flags .plane`, `Γ_P δ ↦ δ⁻¹⟨e₁,e₂⟩`; **`cosetFlag_injective`** (`N ≥ 3`); **`range_cosetFlag`**: its image is the `Γ(N)`-orbit of the standard flag.
* **`planeFlagAt_orbit_iff`**: two integral planes lie in one `Γ(N)`-orbit iff they are related by the face relation `h' = q h γ` of `PlaneFaces N`.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

theorem mapGL_mem_planeParabolic_iff (X : SL(3, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℚ X ∈ parabolic .plane ↔ X ∈ planeBorel := by
  change (_ ∧ _) ↔ _
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · have : (((X : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0 := h0
      exact_mod_cast this
    · have : (((X : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) : ℚ) = 0 := h1
      exact_mod_cast this
  · rintro ⟨h0, h1⟩
    refine ⟨?_, ?_⟩
    · change (((X : Matrix (Fin 3) (Fin 3) ℤ) 2 0 : ℤ) : ℚ) = 0
      rw [h0]; simp
    · change (((X : Matrix (Fin 3) (Fin 3) ℤ) 2 1 : ℤ) : ℚ) = 0
      rw [h1]; simp

/-- Two integral planes coincide iff `h h'⁻¹` lies in `P(ℚ) ∩ SL₃(ℤ)`. -/
theorem planeFlagAt_eq_iff (h h' : SL(3, ℤ)) : planeFlagAt h = planeFlagAt h' ↔ h * h'⁻¹ ∈ planeBorel := by
  change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk _ ↔ _
  rw [QuotientGroup.eq, ← mapGL_mem_planeParabolic_iff]
  simp [map_inv]


section Cosets

variable (N : ℕ)

/-- The flag attached to a coset `Γ_P δ`: `δ⁻¹ ⟨e₁, e₂⟩`. -/
def cosetFlag : PlaneCoset (gammaN N) → Flags .plane :=
  Quotient.lift (fun δ : gammaN N => planeFlagAt δ.1) (by
    intro a b hab
    have h : b.1 * a.1⁻¹ ∈ planeStab := (Subgroup.mem_subgroupOf.mp (QuotientGroup.rightRel_apply.mp hab))
    apply (planeFlagAt_eq_iff a.1 b.1).mpr
    have : a.1 * b.1⁻¹ = (b.1 * a.1⁻¹)⁻¹ := by group
    rw [this]
    exact planeBorel.inv_mem ⟨h.1, h.2.1⟩)

theorem cosetFlag_mk (δ : gammaN N) : cosetFlag N (Quotient.mk _ δ) = planeFlagAt δ.1 := rfl

/-- **R2, injectivity** (`N ≥ 3`): the map from the cosets `Γ_P\Γ(N)` to rational plane flags is injective: distinct cosets are distinct planes
(`Γ(N) ∩ P(ℚ) = Γ_P` only for `N ≥ 3`). -/
theorem cosetFlag_injective (hN : 3 ≤ N) : Function.Injective (cosetFlag N) := by
  intro c c'
  induction c using Quotient.inductionOn with
  | _ a =>
    induction c' using Quotient.inductionOn with
    | _ b =>
      intro h
      have h1 : a.1 * b.1⁻¹ ∈ planeBorel := (planeFlagAt_eq_iff a.1 b.1).mp h
      have h2 : a.1 * b.1⁻¹ ∈ gammaN N := (gammaN N).mul_mem a.2 ((gammaN N).inv_mem b.2)
      have h3 : a.1 * b.1⁻¹ ∈ planeStab := mem_planeStab_of_gammaN hN h2 h1.1 h1.2
      apply Quotient.sound
      refine QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_)
      have : (b.1 * a.1⁻¹) = (a.1 * b.1⁻¹)⁻¹ := by group
      change b.1 * a.1⁻¹ ∈ planeStab
      rw [this]
      exact planeStab.inv_mem h3

/-- **The image of the cosets is the `Γ(N)`-orbit of the standard flag.** -/
theorem range_cosetFlag :
    Set.range (cosetFlag N) =
      {F | ∃ γ ∈ gammaN N, F = Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt 1} := by
  ext F
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn with
    | _ a =>
      refine ⟨a.1⁻¹, (gammaN N).inv_mem a.2, ?_⟩
      change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ a.1⁻¹) : Flags .plane) = _
      change _ = Matrix.SpecialLinearGroup.mapGL ℚ a.1⁻¹ • (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (1 : SL(3, ℤ))⁻¹) : Flags .plane)
      simp
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨Quotient.mk _ ⟨γ⁻¹, (gammaN N).inv_mem hγ⟩, ?_⟩
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (γ⁻¹)⁻¹) : Flags .plane) = _
    change _ = Matrix.SpecialLinearGroup.mapGL ℚ γ • (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ (1 : SL(3, ℤ))⁻¹) : Flags .plane)
    simp

/-- **The orbit relation on integral planes is the face relation** `h' = q h γ`, `q ∈ P(ℚ) ∩ SL₃(ℤ)`, `γ ∈ Γ(N)`. -/
theorem planeFlagAt_orbit_iff (h h' : SL(3, ℤ)) :
    (∃ γ ∈ gammaN N, planeFlagAt h' = Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt h) ↔
      ∃ q ∈ planeBorel, ∃ γ ∈ gammaN N, h' = q * h * γ := by
  have key : ∀ γ : SL(3, ℤ), Matrix.SpecialLinearGroup.mapGL ℚ γ • planeFlagAt h = planeFlagAt (h * γ⁻¹) := by
    intro γ
    change _ • (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = QuotientGroup.mk _
    change (QuotientGroup.mk (Matrix.SpecialLinearGroup.mapGL ℚ γ * Matrix.SpecialLinearGroup.mapGL ℚ h⁻¹) : Flags .plane) = _
    simp [map_inv, map_mul]
  constructor
  · rintro ⟨γ, hγ, e⟩
    rw [key, planeFlagAt_eq_iff] at e
    refine ⟨h' * (h * γ⁻¹)⁻¹, e, γ⁻¹, (gammaN N).inv_mem hγ, ?_⟩
    group
  · rintro ⟨q, hq, γ, hγ, rfl⟩
    refine ⟨γ⁻¹, (gammaN N).inv_mem hγ, ?_⟩
    rw [key, planeFlagAt_eq_iff]
    simpa [mul_assoc] using planeBorel.inv_mem hq

end Cosets

end TernaryPeriodPolynomials.Argument.FormClassK
