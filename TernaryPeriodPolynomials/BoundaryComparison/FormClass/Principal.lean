module

public import TernaryPeriodPolynomials.BoundaryComparison.FormClass.Transfer
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.PlaneFaceDescent
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.Statement

@[expose] public section


/-!
# `Γ(N)` as the principal subgroup `Γ ∩ Γ(N)` of the level group, and the transported form class

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.FormSeriesModel
open TernaryPeriodPolynomials.Argument.ConvergenceC4

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormClassK

section Principal

/-- `Γ(N) → Γ ∩ Γ(N)`, `γ ↦ γ` as a rational matrix. -/
def toPrincipal (N : ℕ) (h3 : 3 ∣ N) : gammaN N →* levelPrincipal N where
  toFun p := ⟨Matrix.SpecialLinearGroup.mapGL ℚ p.1, mapGL_mem_levelPrincipal N h3 p.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem toPrincipal_val (N : ℕ) (h3 : 3 ∣ N) (p : gammaN N) :
    ((toPrincipal N h3 p : levelPrincipal N) : RationalGL3) = Matrix.SpecialLinearGroup.mapGL ℚ p.1 := rfl

theorem toPrincipal_injective (N : ℕ) (h3 : 3 ∣ N) : Function.Injective (toPrincipal N h3) := by
  intro a b hab
  have h1 := congrArg (fun x : levelPrincipal N => ((x : RationalGL3).val : Matrix (Fin 3) (Fin 3) ℚ)) hab
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have := congrFun (congrFun h1 i) j
  change (((a.1 : SL(3, ℤ)) i j : ℤ) : ℚ) = (((b.1 : SL(3, ℤ)) i j : ℤ) : ℚ) at this
  exact_mod_cast this

theorem toPrincipal_surjective (N : ℕ) (h3 : 3 ∣ N) (hN : 3 ≤ N) : Function.Surjective (toPrincipal N h3) := by
  rintro ⟨x, g, hg, hgx⟩
  have hred : ∀ i j, (((g.1.val i j : ℤ)) : ZMod N) = (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
    intro i j
    have := congrArg (fun y : GL (Fin 3) (ZMod N) => (y.val : Matrix (Fin 3) (Fin 3) (ZMod N)) i j)
      (MonoidHom.mem_ker.mp hg)
    exact this
  have hdet1 : g.1.val.det = 1 := by
    have hu : IsUnit g.1.val.det := (Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit
    have hmod : ((g.1.val.det : ℤ) : ZMod N) = 1 := by
      have : (g.1.val.map (Int.castRingHom (ZMod N))).det = ((g.1.val.det : ℤ) : ZMod N) :=
        (RingHom.map_det (Int.castRingHom (ZMod N)) g.1.val).symm
      rw [← this]
      have hm : g.1.val.map (Int.castRingHom (ZMod N)) = 1 := by
        ext i j; exact hred i j
      rw [hm, Matrix.det_one]
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · rw [h1] at hmod
      have h2 : ((-1 : ℤ) : ZMod N) = ((1 : ℤ) : ZMod N) := by simpa using hmod
      have h3' := (ZMod.intCast_eq_intCast_iff_dvd_sub (-1) 1 N).mp h2
      have h4 : (N : ℤ) ∣ 2 := by
        have : (1 : ℤ) - -1 = 2 := by norm_num
        rwa [this] at h3'
      have h5 := Int.le_of_dvd (by norm_num) h4
      omega
  let p : SL(3, ℤ) := ⟨g.1.val, hdet1⟩
  have hpN : p ∈ gammaN N := by
    rw [mem_gammaN]
    intro i j
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
    rw [Int.cast_sub, sub_eq_zero]
    have h1 : (((1 : Matrix (Fin 3) (Fin 3) ℤ) i j : ℤ) : ZMod N) =
        (1 : Matrix (Fin 3) (Fin 3) (ZMod N)) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    rw [h1]
    exact hred i j
  have hxp : Matrix.SpecialLinearGroup.mapGL ℚ p = x := by
    rw [← hgx]
    apply Units.ext
    ext i j
    rfl
  exact ⟨⟨p, hpN⟩, Subtype.ext hxp⟩

/-- **`Γ(N) ≅ Γ ∩ Γ(N)`** for `3 ∣ N` (so `N ≥ 3`, hence `det = 1` on the principal congruence subgroup of
`GL₃(ℤ)`). -/
def principalEquiv (N : ℕ) (h3 : 3 ∣ N) (hN : 3 ≤ N) : gammaN N ≃* levelPrincipal N :=
  MulEquiv.ofBijective (toPrincipal N h3) ⟨toPrincipal_injective N h3, toPrincipal_surjective N h3 hN⟩

end Principal

end TernaryPeriodPolynomials.Argument.FormClassK
