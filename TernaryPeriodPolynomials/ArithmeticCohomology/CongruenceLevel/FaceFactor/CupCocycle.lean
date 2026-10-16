module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.DiagSystem

@[expose] public section


/-!
# The cup product of two cocycles is a cocycle

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ] {C : ChainComplex (Rep.{0} ℚ Γ) ℕ} (S : DiagSystem C)
  {W W' T : Rep.{0} ℚ Γ}

/-- **The cup product of two degree-two cocycles is a degree-four cocycle**: `d₅ ≫ Δ₂,₂ ≫ (z ⊗ z') ≫ π = 0`. -/
theorem cup_cocycle (z : C.X 2 ⟶ W) (hz : C.d 3 2 ≫ z = 0) (z' : C.X 2 ⟶ W') (hz' : C.d 3 2 ≫ z' = 0)
    (π : W ⊗ W' ⟶ T) : C.d 5 4 ≫ S.Δ 2 2 4 rfl ≫ (z ⊗ₘ z') ≫ π = 0 := by
  rw [← Category.assoc, S.leibniz 2 2 4 rfl]
  simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc]
  have h1 : (C.d 3 2 ▷ C.X 2) ≫ (z ⊗ₘ z') = 0 := by
    rw [tensorHom_def, ← Category.assoc, ← comp_whiskerRight, hz, MonoidalPreadditive.zero_whiskerRight, zero_comp]
  have h2 : (C.X 2 ◁ C.d 3 2) ≫ (z ⊗ₘ z') = 0 := by
    rw [tensorHom_def, ← Category.assoc, whisker_exchange, Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hz',
      MonoidalPreadditive.whiskerLeft_zero, comp_zero]
  have h1' : (C.d 3 2 ▷ C.X 2) ≫ (z ⊗ₘ z') ≫ π = 0 := by rw [← Category.assoc, h1, zero_comp]
  have h2' : (C.X 2 ◁ C.d 3 2) ≫ (z ⊗ₘ z') ≫ π = 0 := by rw [← Category.assoc, h2, zero_comp]
  rw [h1', h2']
  simp

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
