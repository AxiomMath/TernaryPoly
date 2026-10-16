module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.Push.ConeLeibniz

@[expose] public section


/-!
# Diagonal-compatible maps out of a pushout cone

A chain map `g : K ⟶ D` out of a pushout cone which kills the shifted `A`-coordinate and restricts to diagonal-strict
maps `gL`, `gP` on the `L`- and `P`-strata is diagonal-strict for the cone diagonal.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits MonoidalCategory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat

variable {Γ : Type} [Group Γ]
  {A L P K D : ChainComplex (Rep.{0} ℚ Γ) ℕ} {a : A ⟶ L} {b : A ⟶ P}

namespace PushCone

variable (𝒞 : PushCone A L P K a b) (SA : DiagSystem A) (SL : DiagSystem L) (SP : DiagSystem P)
  (SD : DiagSystem D)

theorem zero_tensorHom' {X Y Z W : Rep.{0} ℚ Γ} (g : Z ⟶ W) : (0 : X ⟶ Y) ⊗ₘ g = 0 := by
  rw [MonoidalCategory.tensorHom_def, MonoidalPreadditive.zero_whiskerRight, zero_comp]

theorem tensorHom_zero' {X Y Z W : Rep.{0} ℚ Γ} (f : X ⟶ Y) : f ⊗ₘ (0 : Z ⟶ W) = 0 := by
  rw [MonoidalCategory.tensorHom_def, MonoidalPreadditive.whiskerLeft_zero, comp_zero]

/-- A chain map out of a pushout cone, vanishing on the corner coordinate and diagonal-strict on the other two,
is diagonal-strict. -/
theorem map_strict (g : K ⟶ D) (gL : L ⟶ D) (gP : P ⟶ D)
    (hA : ∀ n, 𝒞.iA n ≫ g.f (n+1) = 0) (hL : ∀ n, 𝒞.iL n ≫ g.f n = gL.f n)
    (hP : ∀ n, 𝒞.iP n ≫ g.f n = gP.f n)
    (sL : ∀ p q n (h : p + q = n), gL.f n ≫ SD.Δ p q n h = SL.Δ p q n h ≫ (gL.f p ⊗ₘ gL.f q))
    (sP : ∀ p q n (h : p + q = n), gP.f n ≫ SD.Δ p q n h = SP.Δ p q n h ≫ (gP.f p ⊗ₘ gP.f q))
    (p q n : ℕ) (h : p + q = n) :
    g.f n ≫ SD.Δ p q n h = 𝒞.Δ SA SL SP p q n h ≫ (g.f p ⊗ₘ g.f q) := by
  have keyL : ∀ (m : ℕ) (hm : p + q = m), 𝒞.iL m ≫ g.f m ≫ SD.Δ p q m hm =
      𝒞.iL m ≫ 𝒞.Δ SA SL SP p q m hm ≫ (g.f p ⊗ₘ g.f q) := by
    intro m hm
    rw [← Category.assoc, hL, sL, iL_Δ'_assoc, MonoidalCategory.tensorHom_comp_tensorHom, hL, hL]
  have keyP : ∀ (m : ℕ) (hm : p + q = m), 𝒞.iP m ≫ g.f m ≫ SD.Δ p q m hm =
      𝒞.iP m ≫ 𝒞.Δ SA SL SP p q m hm ≫ (g.f p ⊗ₘ g.f q) := by
    intro m hm
    rw [← Category.assoc, hP, sP, iP_Δ'_assoc, MonoidalCategory.tensorHom_comp_tensorHom, hP, hP]
  cases n with
  | zero => exact 𝒞.ext0 (keyL 0 h) (keyP 0 h)
  | succ n' =>
    apply 𝒞.ext n'
    · rw [← Category.assoc, hA, zero_comp, ← Category.assoc, iA_Δ]
      have hI : 𝒞.tIc SA p q n' h ≫ (g.f p ⊗ₘ g.f q) = 0 := by
        cases p with
        | zero => simp [tIc]
        | succ p' =>
          unfold tIc tI
          rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hA p', zero_tensorHom', comp_zero]
      have hII : 𝒞.tIIc SA p q n' h ≫ (g.f p ⊗ₘ g.f q) = 0 := by
        cases q with
        | zero => simp [tIIc]
        | succ q' =>
          unfold tIIc tII
          rw [Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, hA q', tensorHom_zero', comp_zero]
      unfold aPart
      rw [Preadditive.add_comp, Preadditive.zsmul_comp, hI, hII, smul_zero, add_zero]
    · exact keyL (n'+1) h
    · exact keyP (n'+1) h

end PushCone

end TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
