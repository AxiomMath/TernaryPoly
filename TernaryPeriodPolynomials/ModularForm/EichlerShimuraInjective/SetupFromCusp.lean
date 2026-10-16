module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimuraInjective.FaceInjective

@[expose] public section


/-!
# The standing hypotheses from a coboundary relation of cusp forms

`setup_of_coboundary`.

Eichler-Shimura theory is used for injectivity of the seed map at level `Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section
namespace TernaryPeriodPolynomials.Argument.EichlerShimuraInj

variable (N : ℕ) [NeZero N] (n : ℕ)

omit [NeZero N] in
theorem setup_of_coboundary
    (F G : CuspForm (LamGL (CongruenceSubgroup.Gamma N)) ((n + 3 : ℕ) : ℤ))
    (v : binRep (CongruenceSubgroup.Gamma N) n)
    (hv : ∀ m : CongruenceSubgroup.Gamma N,
      (holCocycle F).1 m + (antiholCocycle G).1 m = (binRep (CongruenceSubgroup.Gamma N) n).ρ m v - v) :
    Setup (CongruenceSubgroup.Gamma N) n (cuspH (LamGL (CongruenceSubgroup.Gamma N)) n F)
      (cuspH (LamGL (CongruenceSubgroup.Gamma N)) n G) (momentPrim (LamGL (CongruenceSubgroup.Gamma N)) n F)
      (momentPrim (LamGL (CongruenceSubgroup.Gamma N)) n G) (bvalΛ v) where
  hf := cuspH_holo _ n F
  hg := cuspH_holo _ n G
  mf γ hγ z hz := modular_of_slashInvariant (LamGL (CongruenceSubgroup.Gamma N)) (n + 3) F (toR γ)
    (Subgroup.mem_map_of_mem _ hγ) z hz
  mg γ hγ z hz := modular_of_slashInvariant (LamGL (CongruenceSubgroup.Gamma N)) (n + 3) G (toR γ)
    (Subgroup.mem_map_of_mem _ hγ) z hz
  dGf j z hz := momentPrim_hasDerivAt _ n F j z hz
  dGg j z hz := momentPrim_hasDerivAt _ n G j z hz
  Gf0 j := momentPrim_zero _ n F j
  Gg0 j := momentPrim_zero _ n G j
  vh := (MvPolynomial.mem_homogeneousSubmodule _ _).mp v.2
  cob γ hγ := by
    have h1 := congrArg bvalΛ (hv ⟨γ, hγ⟩)
    have e2 : bvalΛ ((binRep (CongruenceSubgroup.Gamma N) n).ρ ⟨γ, hγ⟩ v - v) =
        MvPolynomial.bind₁ (invCoordPoly (toR γ)) (bvalΛ v) - bvalΛ v := by
      have := modularBinaryRep_coe (n + 1) γ v
      exact congrArg (fun p => p - bvalΛ v) this
    rw [e2] at h1
    exact h1

end TernaryPeriodPolynomials.Argument.EichlerShimuraInj
