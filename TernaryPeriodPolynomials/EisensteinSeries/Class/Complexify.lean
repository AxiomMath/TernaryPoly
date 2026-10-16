module

public import TernaryPeriodPolynomials.EisensteinSeries.Class.Setup
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.Seed.Relative

@[expose] public section


/-!
# Complexification of the de Rham classes of `Γ ⊂ SL₃(ℤ)`

The
class of `ℰ_P(ω_h)` lives in `H²(Γ, E)` with `E = Sym^n((ℂ³)*) ⊗ det⁻¹` a complex representation,
while the de Rham zig-zag produces classes with coefficients the REAL representation `Coef n`
(`gammaRho Γ n`). As for the seed classes (`GammaNSeed.complexifyG`), `complexify` is the
`ℝ`-linear map `H²(Γ, E_n)_ℝ → H²(Γ, E_n)_ℂ` which is the identity on 2-cocycles.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.SeedC3S4c (realDescent realDescent_apply)

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinClass

open TernaryPeriodPolynomials.Argument.SeedC3

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)

/-- The complex coefficient representation `E_n` of `Γ` (as a representation of `Rep ℂ Γ`). -/
abbrev gammaRep : Rep ℂ Γ := Rep.of (gammaRhoC Γ n)

/-- Coefficients, real carrier to complex carrier (the identity). -/
def cxVec (x : Rep.of (gammaRho Γ n)) : gammaRep Γ n := x

/-- Real 2-cocycles of `Γ` with values in `E_n` are complex 2-cocycles. -/
def cxCocycles : cocycles₂ (Rep.of (gammaRho Γ n)) →ₗ[ℝ] cocycles₂ (gammaRep Γ n) where
  toFun c := ⟨fun p => cxVec Γ n (c.1 p), (mem_cocycles₂_iff _).2 (fun g h j => by
    have e := (mem_cocycles₂_iff _).1 c.2 g h j
    exact e)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Complexification** `H²(Γ, E_n)_ℝ → H²(Γ, E_n)_ℂ`, the identity on cocycles. -/
def complexify : H2 (Rep.of (gammaRho Γ n)) →ₗ[ℝ] H2 (gammaRep Γ n) :=
  realDescent (H2π (Rep.of (gammaRho Γ n))).hom
    (fun x => H2_induction_on x (fun c => ⟨c, rfl⟩))
    (((H2π (gammaRep Γ n)).hom.restrictScalars ℝ).comp (cxCocycles Γ n))
    (fun a b hab => by
      have h : H2π (Rep.of (gammaRho Γ n)) a = H2π (Rep.of (gammaRho Γ n)) b := hab
      rw [H2π_eq_iff] at h
      obtain ⟨y, hy⟩ := h
      change H2π (gammaRep Γ n) (cxCocycles Γ n a) = H2π (gammaRep Γ n) (cxCocycles Γ n b)
      rw [H2π_eq_iff]
      refine ⟨fun g => cxVec Γ n (y g), ?_⟩
      funext p
      have hp := congrFun hy p
      simp only [d₁₂_hom_apply] at hp ⊢
      exact hp)

theorem complexify_H2π (c : cocycles₂ (Rep.of (gammaRho Γ n))) :
    complexify Γ n (H2π (Rep.of (gammaRho Γ n)) c) = H2π (gammaRep Γ n) (cxCocycles Γ n c) :=
  realDescent_apply _ _ _ _ c

end TernaryPeriodPolynomials.Argument.EisensteinClass
