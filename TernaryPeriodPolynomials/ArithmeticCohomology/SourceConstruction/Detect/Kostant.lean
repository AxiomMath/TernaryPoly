module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Detect.Edge
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


/-!
# The Kostant law from the derivative form

The Kostant law of `DetectEdge` (Euler identity for the restriction of the radical cocycle to the
two generators of the radical lattice) follows from the elementary derivative form
`res λ(u(e_i)) q = κ ∂_i q`, by Euler's identity for homogeneous polynomials.  For the radical
cocycle `λ(u(s,t)) q = ((ρ u)(ι q) - ι q) / x₂` one has
`res λ(u(s,t)) q = -(s ∂₀ q + t ∂₁ q)`, i.e. `κ = -1`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.SourceConstruction

theorem kostantLaw_of_derivative {n : ℕ} {lam : RadicalLattice → (PlaneQ n →ₗ[ℂ] PlaneV n)} {κ : ℂ}
    (h0 : ∀ q : PlaneQ n,
      (binaryHomogeneousRestrict n (lam radicalLatticeFirst q)).val =
        κ • MvPolynomial.pderiv (0 : Fin 2) q.val)
    (h1 : ∀ q : PlaneQ n,
      (binaryHomogeneousRestrict n (lam radicalLatticeSecond q)).val =
        κ • MvPolynomial.pderiv (1 : Fin 2) q.val) :
    KostantLaw n lam κ := by
  intro q
  have hq : q.val.IsHomogeneous (n + 1) := (MvPolynomial.mem_homogeneousSubmodule _ _).mp q.2
  have euler := hq.sum_X_mul_pderiv
  rw [Fin.sum_univ_two] at euler
  have hne : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [h0, h1, mul_smul_comm, mul_smul_comm, ← smul_add, euler,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  congr 1
  push_cast
  linear_combination κ * mul_inv_cancel₀ hne

end TernaryPeriodPolynomials.SourceConstruction
