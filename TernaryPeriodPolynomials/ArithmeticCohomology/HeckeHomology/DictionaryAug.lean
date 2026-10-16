module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModel

@[expose] public section


/-!
# The augmentation of the coinvariant complex `(A ⊗ R)_Γ → A_Γ`

Formalized by Claude Sonnet 5.5.
Used by `DictionaryTernary`/`DictionaryBinary` to read the chain-level Hecke operator on `H₀`, i.e. on coinvariants.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open CategoryTheory Representation Representation.Coinvariants

section Aug

variable {Γ : Type} [Group Γ] (A R0 : Rep.{0} ℚ Γ) (ε : R0 ⟶ Rep.trivial ℚ Γ ℚ)

/-- The augmentation `(A ⊗ R₀)_Γ → A_Γ`, `[m ⊗ r] ↦ ε(r) [m]`. -/
def augMap : Coinvariants (A.ρ.tprod R0.ρ) →ₗ[ℚ] Coinvariants A.ρ :=
  Coinvariants.lift _
    (TensorProduct.lift (LinearMap.mk₂ ℚ (fun (m : A) (r : R0) => ε.hom r • Coinvariants.mk A.ρ m)
      (fun m m' r => by simp [smul_add]) (fun c m r => by rw [map_smul]; exact smul_comm _ _ _)
      (fun m r r' => by simp [add_smul]) (fun c m r => by simp [smul_smul])))
    (fun g => by
      refine TensorProduct.ext' fun m r => ?_
      have h1 : ε.hom (R0.ρ g r) = ε.hom r := Rep.hom_comm_apply ε g r
      change ε.hom (R0.ρ g r) • Coinvariants.mk A.ρ (A.ρ g m) = ε.hom r • Coinvariants.mk A.ρ m
      rw [h1, Coinvariants.mk_self_apply])

theorem augMap_mk (m : A) (r : R0) :
    augMap A R0 ε (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) = ε.hom r • Coinvariants.mk A.ρ m := rfl

/-- The augmentation `R₀ → 1` of a resolution of the trivial module. -/
def epsOf {Γ : Type} [Group Γ] (R : ProjectiveResolution (Rep.trivial ℚ Γ ℚ)) :
    R.complex.X 0 ⟶ Rep.trivial ℚ Γ ℚ := R.π.f 0

end Aug

section Right

variable {G : Type} [Group G] (M : Rep.{0} ℚ G)

/-- **The left/right dictionary.**  A right module `M` (the paper's convention: `D_d` "with the right substitution action",
fibre action `q ↦ det(C) q(C(b,c))`) is the left module `ρ(g) m = m · g⁻¹` used in this development; conversely a left module `M` becomes
the right module `m · g := ρ(g⁻¹) m`. -/
def rightAct (m : M) (g : G) : M := M.ρ g⁻¹ m

theorem rightAct_one (m : M) : rightAct M m 1 = m := by simp [rightAct]

theorem rightAct_mul (m : M) (g h : G) : rightAct M m (g * h) = rightAct M (rightAct M m g) h := by
  simp only [rightAct, mul_inv_rev, map_mul]
  rfl

theorem rightAct_ρ (m : M) (g : G) : M.ρ g m = rightAct M m g⁻¹ := by simp [rightAct]

end Right

end TernaryPeriodPolynomials.Argument.HeckeHomology
