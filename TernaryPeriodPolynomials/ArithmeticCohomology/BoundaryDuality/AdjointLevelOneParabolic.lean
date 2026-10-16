module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityEdgeLevelOne
public import TernaryPeriodPolynomials.EisensteinSeries.LevelOne.EisensteinScalar

@[expose] public section


/-!
# The Hecke operators preserve the parabolic classes of `GL₂(ℤ)`

A class of `H¹(GL₂(ℤ), Sym^d ⊗ det^σ)` is parabolic exactly when the boundary functional
`β = [z] ↦ ℓ(z(T))` kills it, where `ℓ` is the evaluation of a binary form at `(1, 0)`: the
forms of `Sym^d` with `ℓ = 0` are exactly the image of `T - 1`.  The functional `β` is a Hecke
eigenfunctional (`β ∘ T_p = q_p β` with the Eisenstein eigenvalue `q_p`), hence its kernel is
stable under every Hecke operator `T_p`.  So `T_p` restricts to an endomorphism `parabolicHecke` of
the space of parabolic classes, on which the parabolic cup pairing is defined.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne

open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.BoundaryFunctional
open TernaryPeriodPolynomials.Spectral.LevelOneESDimension
open TernaryPeriodPolynomials.Spectral.LevelOneHeckeH1 (arithmeticHecke)
open TernaryPeriodPolynomials.LevelOneEisenstein (betaGL betaGL_arithmeticHecke)
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality.LevelOne

/-- The boundary functional `ℓ` kills `(T - 1) u`. -/
theorem ell_rho_T_sub (d : ℕ) (σ : ℤ) (u : arithmeticBinaryRep d σ) :
    ell d ((arithmeticBinaryRep d σ).ρ (toGL ModularGroup.T) u - u) = 0 := by
  have hmem : (Binary.homogeneousAction d σ (SymFixed.upperC 1) - 1) u ∈
      LinearMap.ker (SymFixed.evalAt (m := d) ![1, 0]) := by
    rw [← FullBound.movedSpace_upper_eq σ one_ne_zero]
    exact ⟨u, rfl⟩
  rw [rho_T_eq]
  exact LinearMap.mem_ker.mp hmem

/-- The boundary functional of a class is the value of `ℓ` at a representative cocycle at `T`. -/
theorem betaGL_H1π (d : ℕ) (σ : ℤ) (z : groupCohomology.cocycles₁ (arithmeticBinaryRep d σ)) :
    betaGL d σ (groupCohomology.H1π (arithmeticBinaryRep d σ) z) =
      ell d (z (toGL ModularGroup.T)) := by
  show beta d σ (restriction d σ σ (groupCohomology.H1π (arithmeticBinaryRep d σ) z)) = _
  rw [restriction_apply, beta_H1π]
  rfl

/-- **Parabolic classes are killed by the boundary functional.** -/
theorem betaGL_eq_zero_of_mem_parabolicH1 {d : ℕ} {σ : ℤ}
    {x : groupCohomology.H1 (arithmeticBinaryRep d σ)}
    (hx : x ∈ parabolicH1 (arithmeticBinaryRep d σ)) : betaGL d σ x = 0 := by
  obtain ⟨z, ⟨u, hu⟩, rfl⟩ := (mem_parabolicH1_iff _ x).1 hx
  show betaGL d σ (groupCohomology.H1π (arithmeticBinaryRep d σ) z) = 0
  rw [betaGL_H1π]
  have hu' : z (toGL ModularGroup.T) =
      (arithmeticBinaryRep d σ).ρ (toGL ModularGroup.T) u - u := hu
  rw [hu']
  exact ell_rho_T_sub d σ u

/-- **A class is parabolic iff the boundary functional kills it.** -/
theorem mem_parabolicH1_iff_betaGL_eq_zero {d : ℕ} {σ : ℤ}
    (x : groupCohomology.H1 (arithmeticBinaryRep d σ)) :
    x ∈ parabolicH1 (arithmeticBinaryRep d σ) ↔ betaGL d σ x = 0 :=
  ⟨betaGL_eq_zero_of_mem_parabolicH1, mem_parabolicH1_of_betaGL_eq_zero⟩

/-- **The Hecke operator `T_p` preserves the parabolic classes.** -/
theorem arithmeticHecke_mem_parabolicH1 (d : ℕ) (σ : ℤ) (p : Nat.Primes)
    {x : groupCohomology.H1 (arithmeticBinaryRep d σ)}
    (hx : x ∈ parabolicH1 (arithmeticBinaryRep d σ)) :
    arithmeticHecke d σ p x ∈ parabolicH1 (arithmeticBinaryRep d σ) :=
  mem_parabolicH1_of_betaGL_eq_zero
    (by rw [betaGL_arithmeticHecke, betaGL_eq_zero_of_mem_parabolicH1 hx, mul_zero])

/-- **The Hecke operator `T_p` on the parabolic classes of `H¹(GL₂(ℤ), Sym^d ⊗ det^σ)`.** -/
def parabolicHecke (d : ℕ) (σ : ℤ) (p : Nat.Primes) :
    Module.End ℂ (parabolicH1 (arithmeticBinaryRep d σ)) :=
  LinearMap.restrict (arithmeticHecke d σ p)
    (fun _ hx => arithmeticHecke_mem_parabolicH1 d σ p hx)

/-- The parabolic Hecke operator is the restriction of `T_p`. -/
theorem coe_parabolicHecke (d : ℕ) (σ : ℤ) (p : Nat.Primes)
    (x : parabolicH1 (arithmeticBinaryRep d σ)) :
    ((parabolicHecke d σ p x : parabolicH1 (arithmeticBinaryRep d σ)) :
        groupCohomology.H1 (arithmeticBinaryRep d σ)) = arithmeticHecke d σ p x :=
  rfl

end TernaryPeriodPolynomials.BoundaryDuality.AdjointLevelOne
