module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.SpanTransfer
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem

@[expose] public section


/-!
# The pairing functional of two degree-two cocycles depends only on the coinvariant homology class

For a diagonal system `SD` on `D`, cocycles `b : D.X 2 ⟶ W`, `a : D.X 2 ⟶ W'` and an invariant pairing
`π : W ⊗ W' ⟶ 𝟙_`, the Γ-equivariant functional `pairFun = Δ_{2,2} ≫ (b ⊗ a) ≫ π` on `D.X 4` kills the boundaries
(`pairFun_boundary`), hence it takes proportional values on chains whose coinvariant classes are proportional modulo
boundaries (`pairFun_eq_of_mem_range`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ] {D : ChainComplex (Rep.{0} ℚ Γ) ℕ} (SD : DiagSystem D) {W W' : Rep.{0} ℚ Γ}
  (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ))

/-- The invariant functional `π ∘ (b ⊗ a) ∘ Δ_{2,2}` on the degree-four chains. -/
def pairFun (b : D.X 2 ⟶ W) (a : D.X 2 ⟶ W') : D.X 4 ⟶ 𝟙_ (Rep.{0} ℚ Γ) :=
  SD.Δ 2 2 4 rfl ≫ (b ⊗ₘ a) ≫ π

theorem pairFun_boundary (b : D.X 2 ⟶ W) (hb : D.d 3 2 ≫ b = 0) (a : D.X 2 ⟶ W') (ha : D.d 3 2 ≫ a = 0) :
    D.d 5 4 ≫ pairFun SD π b a = 0 := by
  unfold pairFun
  rw [← Category.assoc, SD.leibniz 2 2 4 rfl]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
  have h1 : (D.d (2+1) 2 ▷ D.X 2) ≫ (b ⊗ₘ a) ≫ π = 0 := by
    rw [← Category.assoc, MonoidalCategory.tensorHom_def, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight,
      hb, MonoidalPreadditive.zero_whiskerRight, zero_comp, zero_comp]
  have h2 : (D.X 2 ◁ D.d (2+1) 2) ≫ (b ⊗ₘ a) ≫ π = 0 := by
    rw [MonoidalCategory.tensorHom_def']
    simp only [Category.assoc]
    rw [← Category.assoc (D.X 2 ◁ D.d (2+1) 2), ← MonoidalCategory.whiskerLeft_comp, ha,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  rw [h1, h2]
  simp

theorem pairFun_eq_of_mem_range (b : D.X 2 ⟶ W) (hb : D.d 3 2 ≫ b = 0) (a : D.X 2 ⟶ W') (ha : D.d 3 2 ≫ a = 0)
    (ω₁ ω₂ : D.X 4) (c : ℚ)
    (h : Representation.Coinvariants.mk (D.X 4).ρ ω₁ - c • Representation.Coinvariants.mk (D.X 4).ρ ω₂ ∈
      LinearMap.range (coinvD D 5 4)) :
    (pairFun SD π b a).hom ω₁ = c • (pairFun SD π b a).hom ω₂ := by
  have h0 := coinvHom_eq_zero_of_mem_range (P := D) (pairFun SD π b a) (pairFun_boundary SD π b hb a ha) h
  rw [map_sub, map_smul, coinvHom_apply_mk, coinvHom_apply_mk, sub_eq_zero] at h0
  exact h0

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
