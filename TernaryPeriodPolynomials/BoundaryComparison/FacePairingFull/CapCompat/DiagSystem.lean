module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Thm

@[expose] public section


/-!
# Diagonal systems and the caps they define

A `DiagSystem` on a chain complex `C` of representations is a (counital) Alexander-Whitney type diagonal
`Δ p q n h : C.X n ⟶ C.X p ⊗ C.X q` (`h : p + q = n`) with the Leibniz rule and the right counit law.  Capping
cocycles against the front factor gives a `CapSystem`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]

/-- A counital diagonal on a chain complex of representations. -/
structure DiagSystem (C : ChainComplex (Rep.{0} ℚ Γ) ℕ) where
  Δ : ∀ p q n : ℕ, p + q = n → (C.X n ⟶ C.X p ⊗ C.X q)
  leibniz : ∀ (p q n : ℕ) (h : p + q = n),
    C.d (n+1) n ≫ Δ p q n h =
      Δ (p+1) q (n+1) (by omega) ≫ (C.d (p+1) p ▷ C.X q) +
        ((-1 : ℤ)^p) • (Δ p (q+1) (n+1) (by omega) ≫ (C.X p ◁ C.d (q+1) q))
  eps : C.X 0 ⟶ 𝟙_ (Rep.{0} ℚ Γ)
  eps_d : C.d 1 0 ≫ eps = 0
  counit : ∀ p : ℕ, Δ p 0 p (add_zero p) ≫ (C.X p ◁ eps) ≫ (ρ_ (C.X p)).hom = 𝟙 (C.X p)

variable {C : ChainComplex (Rep.{0} ℚ Γ) ℕ}

/-- The cap system of a diagonal system. -/
def DiagSystem.toCapSystem (S : DiagSystem C) : CapSystem C where
  cap {W} a b _hb q := S.Δ a q (a+q) rfl ≫ (b ▷ C.X q)
  intertwine {W} a b hb q := by
    have h := congrArg (fun φ => φ ≫ (b ▷ C.X q)) (S.leibniz a q (a+q) rfl)
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc] at h
    rw [← MonoidalCategory.comp_whiskerRight, hb, MonoidalPreadditive.zero_whiskerRight, comp_zero,
      zero_add, MonoidalCategory.whisker_exchange] at h
    simp only [Category.assoc]
    exact h
  eps := S.eps
  eps_d := S.eps_d
  counit {W} a b _hb := by
    have h : S.Δ a 0 (a+0) rfl ≫ (C.X a ◁ S.eps) ≫ (ρ_ (C.X a)).hom = 𝟙 (C.X a) := S.counit a
    calc (S.Δ a 0 (a+0) rfl ≫ (b ▷ C.X 0)) ≫ (W ◁ S.eps) ≫ (ρ_ W).hom
        = S.Δ a 0 (a+0) rfl ≫ (C.X a ◁ S.eps) ≫ (b ▷ 𝟙_ (Rep.{0} ℚ Γ)) ≫ (ρ_ W).hom := by
          rw [Category.assoc, ← Category.assoc (b ▷ C.X 0), ← MonoidalCategory.whisker_exchange b S.eps]
          simp only [Category.assoc]
      _ = S.Δ a 0 (a+0) rfl ≫ (C.X a ◁ S.eps) ≫ (ρ_ (C.X a)).hom ≫ b := by
          rw [MonoidalCategory.rightUnitor_naturality]
      _ = b := by
          calc S.Δ a 0 (a+0) rfl ≫ (C.X a ◁ S.eps) ≫ (ρ_ (C.X a)).hom ≫ b
              = (S.Δ a 0 (a+0) rfl ≫ (C.X a ◁ S.eps) ≫ (ρ_ (C.X a)).hom) ≫ b := by simp only [Category.assoc]
            _ = b := by rw [h]; simp

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
