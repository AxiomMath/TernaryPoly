module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.AntiHolomorphic
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneCusps

@[expose] public section


/-!
# `g5_levelOne` at the other plane cusps: transport of the cocycle class along the conjugation

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (`ar:lem:seed`) at the plane cusps `h⁻¹ P h` ("rationally conjugate the other plane cusps to `P`").

* `isConj_cusp`, `isConj_cusp'`: `Δ_σ = (mapGL σ)⁻¹ Δ_P mapGL σ` for `Δ_σ = realLevel (gammaNPAt N σ)`.
* `cuspCocycle`, `cuspCocycle_apply`: the cocycle `y ↦ ρ(σ⁻¹) C(σ y)` of `realLevel Γ_{σ⁻¹Pσ}`.
* `bridge_cuspCocycle`, `class_transport_cusp`: its class (in Mathlib's `H²(Γ_{σ⁻¹Pσ}, E_n)`) is the pullback of the class of `C` along the conjugation `conjP N σ` with the coefficient comparison `faceMor` (`v ↦ ρ(σ⁻¹) v`, the `faceT`).
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.LevelTransfer

variable (N : ℕ) (n : ℕ) (σ : SL(3, ℤ))

theorem mem_realLevel_iff {Γ : Subgroup SL(3, ℤ)} {x : RealGL3} :
    x ∈ realLevel Γ ↔ ∃ γ ∈ Γ, Matrix.SpecialLinearGroup.mapGL ℝ γ = x := Subgroup.mem_map

/-- `Δ_σ = (mapGL σ)⁻¹ Δ_P mapGL σ`, in the form `x ∈ Δ_P ↔ σ⁻¹ x σ ∈ Δ_σ`. -/
theorem isConj_cusp : IsConj (realLevel (gammaNPAt N σ)) (realLevel (gammaNP N)) (Matrix.SpecialLinearGroup.mapGL ℝ σ) := by
  intro x
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨σ⁻¹ * q * σ, ?_, ?_⟩
    · show σ⁻¹ * q * σ ∈ gammaNPAt N σ
      rw [mem_gammaNPAt]
      have : σ * (σ⁻¹ * q * σ) * σ⁻¹ = q := by group
      rw [this]; exact hq
    · simp [map_mul, map_inv, mul_assoc]
  · rintro ⟨p, hp, hpx⟩
    refine ⟨σ * p * σ⁻¹, hp, ?_⟩
    rw [map_mul, map_mul, map_inv, hpx]
    simp [mul_assoc]

theorem isConj_cusp' : IsConj (realLevel (gammaNP N)) (realLevel (gammaNPAt N σ)) (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ := by
  intro x
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨σ * p * σ⁻¹, hp, ?_⟩
    simp [map_mul, map_inv, mul_assoc]
  · rintro ⟨q, hq, hqx⟩
    refine ⟨σ⁻¹ * q * σ, ?_, ?_⟩
    · show σ⁻¹ * q * σ ∈ gammaNPAt N σ
      rw [mem_gammaNPAt]
      have : σ * (σ⁻¹ * q * σ) * σ⁻¹ = q := by group
      rw [this]; exact hq
    · rw [map_mul, map_mul, map_inv, hqx]
      simp [mul_assoc]

variable (C : cocycles (realLevel (gammaNP N)) (GeneralEisenstein.realCoefficient n))

/-- The cocycle `y ↦ ρ(σ⁻¹) C(σ y)` of the conjugate group `realLevel Γ_{σ⁻¹Pσ}`. -/
def cuspCocycle : cocycles (realLevel (gammaNPAt N σ)) (GeneralEisenstein.realCoefficient n) :=
  actCocycleConj (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ (isConj_cusp' N σ) C

theorem cuspCocycle_apply (y : Fin 3 → RealGL3) :
    (cuspCocycle N n σ C).val.val y = GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹
      (C.val.val (fun i => Matrix.SpecialLinearGroup.mapGL ℝ σ * y i)) := by
  exact (actFun_apply (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ C.val.val y).trans
    (by simp only [inv_inv])

/-- The comparison of coefficient modules for `Γ ≅ realLevel Γ` at an arbitrary subgroup. -/
def repMorAt (Γ : Subgroup SL(3, ℤ)) : Rep.res (realLevelHom Γ)
    (Rep.of ((GeneralEisenstein.realCoefficient n).comp (realLevel Γ).subtype)) ⟶ Rep.of ((ambRep n).comp Γ.subtype) :=
  Rep.ofHom ⟨LinearMap.id, fun _ => rfl⟩

/-- The coefficient comparison `E_n|_{Γ_P} → E_n|_{Γ_{σ⁻¹Pσ}}`, `v ↦ ρ(σ⁻¹) v`, along the conjugation. -/
def faceMor [NeZero N] : Rep.res (conjP N σ).toMonoidHom (gammaNRep N n) ⟶ faceRep N σ n :=
  Rep.ofHom ⟨(faceT σ n).toLinearMap, fun g => LinearMap.ext fun v => faceT_intertwines N σ n g v⟩

theorem actCocycleConj_cusp :
    actCocycleConj (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ)
      (cuspCocycle N n σ C) = C := by
  apply Subtype.ext; apply Subtype.ext
  exact (actFun_mul (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ)
    (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ C.val.val).symm.trans
    (by rw [mul_inv_cancel, actFun_one])

theorem bridge_cuspCocycle :
    bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNPAt N σ))
        (Submodule.Quotient.mk (cuspCocycle N n σ C)) =
      (groupCohomology.map (conjHom (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ))
        (conjRep (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ)) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N)) (Submodule.Quotient.mk C)) := by
  have e := bridge_conj (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ)
    (Submodule.Quotient.mk (cuspCocycle N n σ C))
  have h0 : actH2Conj (GeneralEisenstein.realCoefficient n) (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ)
      (Submodule.Quotient.mk (cuspCocycle N n σ C)) = Submodule.Quotient.mk C := by
    change Submodule.Quotient.mk (actCocycleConj _ _ _ _) = _
    rw [actCocycleConj_cusp]
  rw [h0] at e
  exact e.symm

variable [NeZero N]

omit [NeZero N] in
theorem conjHom_realLevelHom (a : gammaNPAt N σ) :
    conjHom (Matrix.SpecialLinearGroup.mapGL ℝ σ) (isConj_cusp N σ) (realLevelHom (gammaNPAt N σ) a) =
      realLevelHom (gammaNP N) (conjP N σ a) := by
  apply Subtype.ext
  change Matrix.SpecialLinearGroup.mapGL ℝ σ * Matrix.SpecialLinearGroup.mapGL ℝ a.1 * (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹ =
    Matrix.SpecialLinearGroup.mapGL ℝ (σ * a.1 * σ⁻¹)
  simp [map_mul, map_inv]

/-- **The class of the conjugate cocycle is the conjugation transport of the class** (in Mathlib's group cohomology of the plane group of the cusp `σ⁻¹ P σ`). -/
theorem class_transport_cusp :
    (groupCohomology.map (realLevelHom (gammaNPAt N σ)) (repMorAt n (gammaNPAt N σ)) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNPAt N σ))
          (Submodule.Quotient.mk (cuspCocycle N n σ C))) =
      (groupCohomology.map (conjP N σ).toMonoidHom (faceMor N n σ) 2).hom
        ((groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
          (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N)) (Submodule.Quotient.mk C))) := by
  rw [bridge_cuspCocycle]
  generalize bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N)) (Submodule.Quotient.mk C) = x
  induction x using groupCohomology.H2_induction_on with
  | h z =>
    refine ((congrArg _ (groupCohomology.H2π_comp_map_apply _ _ z)).trans
      (groupCohomology.H2π_comp_map_apply _ _ _)).trans (Eq.trans ?_
      ((congrArg _ (groupCohomology.H2π_comp_map_apply _ _ z)).trans
        (groupCohomology.H2π_comp_map_apply _ _ _)).symm)
    refine congrArg (CategoryTheory.ConcreteCategory.hom (groupCohomology.H2π _)) ?_
    apply Subtype.ext
    funext p
    obtain ⟨a, b⟩ := p
    have hz : ∀ (u v : ↥(realLevel (gammaNP N))),
        (GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹) (z.1 (u, v)) =
          (faceT σ n) (z.1 (u, v)) := fun u v => by
      change _ = ambRep n σ⁻¹ _
      simp [ambRep, map_inv]
    have e1 := conjHom_realLevelHom N σ a
    have e2 := conjHom_realLevelHom N σ b
    refine Eq.trans ?_ (hz _ _)
    exact congrArg (fun w => (GeneralEisenstein.realCoefficient n (Matrix.SpecialLinearGroup.mapGL ℝ σ)⁻¹) (z.1 w))
      (Prod.ext e1 e2)

end TernaryPeriodPolynomials.Argument.FormSeedBridge
