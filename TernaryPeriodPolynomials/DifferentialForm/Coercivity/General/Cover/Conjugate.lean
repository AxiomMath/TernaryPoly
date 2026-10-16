module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic

@[expose] public section


/-!
# General coercivity: stability of admissibility

Admissibility passes to subgroups and to conjugates by arbitrary elements of `GL₃(ℝ)` (in
particular by rational matrices), and the trivial group is admissible.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering

variable {Γ Γ' : Subgroup RealGL}

/-- Subgroups of admissible groups are admissible. -/
theorem Admissible.mono (h : Admissible Γ') (hle : Γ ≤ Γ') : Admissible Γ where
  det_one g hg := h.det_one g (hle hg)
  free g hg S hS := h.free g (hle hg) S hS
  transporters C D hC hD :=
    ((h.transporters C D hC hD).preimage (Subgroup.inclusion_injective hle).injOn).subset
      (fun _ hx => hx)

/-- The trivial group is admissible. -/
theorem admissible_bot : Admissible (⊥ : Subgroup RealGL) where
  det_one g hg := by
    rw [Subgroup.mem_bot.mp hg]
    simp
  free g hg _ _ := Subgroup.mem_bot.mp hg
  transporters C D _ _ := by
    refine Set.Finite.subset (Set.finite_singleton (1 : (⊥ : Subgroup RealGL))) ?_
    intro g _
    exact Subsingleton.elim g 1

/-- The conjugate subgroup `g Γ g⁻¹`. -/
def conjSubgroup (Γ : Subgroup RealGL) (g : RealGL) : Subgroup RealGL :=
  Γ.map (MulAut.conj g).toMonoidHom

theorem mem_conjSubgroup {g x : RealGL} : x ∈ conjSubgroup Γ g ↔ ∃ γ ∈ Γ, g * γ * g⁻¹ = x :=
  Iff.rfl

/-- Conjugates of admissible groups by elements of `GL₃(ℝ)` (e.g. rational matrices) are admissible. -/
theorem Admissible.conj (h : Admissible Γ) (g : RealGL) : Admissible (conjSubgroup Γ g) where
  det_one := by
    rintro _ ⟨γ, hγ, rfl⟩
    change (↑(g * γ * g⁻¹) : Matrix (Fin 3) (Fin 3) ℝ).det = 1
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj g γ.val]
    exact h.det_one γ hγ
  free := by
    rintro _ ⟨γ, hγ, rfl⟩ S hS
    have h1 : act γ (act g⁻¹ S) = act g⁻¹ S := by
      have h2 : act g⁻¹ (act (g * γ * g⁻¹) S) = act g⁻¹ S := congrArg _ hS
      rw [act_mul, act_mul, ← act_mul g⁻¹ g, inv_mul_cancel, act_one] at h2
      exact h2
    change g * γ * g⁻¹ = 1
    rw [h.free γ hγ _ h1]
    simp
  transporters C D hC hD := by
    have hC' : IsCompact ((act g⁻¹) '' C) := hC.image (continuous_act g⁻¹)
    have hD' : IsCompact ((act g⁻¹) '' D) := hD.image (continuous_act g⁻¹)
    have hf := (h.transporters _ _ hC' hD').image (fun x : Γ => g * x.1 * g⁻¹)
    refine (hf.preimage (Subtype.val_injective.injOn)).subset ?_
    rintro ⟨_, γ, hγ, rfl⟩ ⟨_, ⟨S, hS, rfl⟩, hT⟩
    refine ⟨⟨γ, hγ⟩, ⟨act (γ : RealGL) (act g⁻¹ S), ⟨act g⁻¹ S, ⟨S, hS, rfl⟩, rfl⟩,
      ⟨act (g * γ * g⁻¹) S, hT, ?_⟩⟩, rfl⟩
    rw [← act_mul, ← act_mul]
    congr 1
    group

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
