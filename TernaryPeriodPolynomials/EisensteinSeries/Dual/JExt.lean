module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFaces
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FacesFull.EdgeSurjective

@[expose] public section


open CategoryTheory groupCohomology
open scoped MatrixGroups

/-!
# `ȷ` as a morphism of the standard split extensions of the line and plane groups

Formalized by Claude Sonnet 5.5.

`ȷ(g) = rt(g⁻¹)` maps the line group `Γ(N) ∩ Q(ℤ)` onto the plane group `Γ(N) ∩ P(ℤ)`; on the radical it is `τ(e, f) = (-f, -e)`
(`jmath_radEltQ`) and on the Levi `σ(a b; c d) = (a -b; -c d)` (`jmath_blockDiagQ`), an automorphism of `Γ₂(N)`.  So `ȷ` is a morphism of split extensions
`(gammaNQInl, gammaNQSect) → (gammaNInl, gammaNSect)` over `(τ, σ)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.Argument.SeedC3S4c TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.GammaNFacesFull TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.GammaNFaces (rt)

/-- The Levi automorphism of `ȷ`: `(a b; c d) ↦ (a -b; -c d)`. -/
def sigmaSL (A : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![(A : Matrix (Fin 2) (Fin 2) ℤ) 0 0, -(A : Matrix (Fin 2) (Fin 2) ℤ) 0 1;
      -(A : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1], by
    have hA : (A : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := A.2
    rw [Matrix.det_fin_two] at hA
    rw [Matrix.det_fin_two_of]
    linear_combination hA⟩

theorem sigmaSL_mul (A B : SL(2, ℤ)) : sigmaSL (A * B) = sigmaSL A * sigmaSL B := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaSL, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem sigmaSL_one : sigmaSL 1 = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaSL]

theorem sigmaSL_sigmaSL (A : SL(2, ℤ)) : sigmaSL (sigmaSL A) = A := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sigmaSL]

theorem sigmaSL_mem {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ CongruenceSubgroup.Gamma N) : sigmaSL A ∈ CongruenceSubgroup.Gamma N := by
  rw [CongruenceSubgroup.Gamma_mem] at hA ⊢
  obtain ⟨h00, h01, h10, h11⟩ := hA
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sigmaSL, h00, h01, h10, h11]

/-- The Levi automorphism `σ` of `Γ₂(N)`. -/
def sigmaGamma (N : ℕ) : ↥(CongruenceSubgroup.Gamma N) →* ↥(CongruenceSubgroup.Gamma N) where
  toFun A := ⟨sigmaSL A.1, sigmaSL_mem A.2⟩
  map_one' := Subtype.ext sigmaSL_one
  map_mul' A B := Subtype.ext (sigmaSL_mul A.1 B.1)

theorem sigmaGamma_involutive (N : ℕ) (A : ↥(CongruenceSubgroup.Gamma N)) : sigmaGamma N (sigmaGamma N A) = A :=
  Subtype.ext (sigmaSL_sigmaSL A.1)

theorem sigmaGamma_bijective (N : ℕ) : Function.Bijective (sigmaGamma N) :=
  Function.Involutive.bijective (sigmaGamma_involutive N)

/-- The radical map of `ȷ`: `(e, f) ↦ (-f, -e)`. -/
def tauRad : RadicalLattice →* RadicalLattice where
  toFun r := Multiplicative.ofAdd (-r.toAdd.2, -r.toAdd.1)
  map_one' := by simp
  map_mul' r s := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_mul]
    constructor <;> ring

theorem tauRad_involutive (r : RadicalLattice) : tauRad (tauRad r) = r := by
  apply Multiplicative.toAdd.injective
  simp [tauRad]

theorem tauRad_bijective : Function.Bijective tauRad := Function.Involutive.bijective tauRad_involutive

theorem jmath_radEltQ (N : ℕ) (r : RadicalLattice) : jmath (radEltQ N r) = radElt N (tauRad r) := by
  have hinv : (radEltQ N r)⁻¹ = radEltQ N r⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← radEltQ_mul, mul_inv_cancel, radEltQ_one])
  apply Subtype.ext
  rw [coe_jmath, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rt, radEltQ, radElt, tauRad, Fin.rev]

theorem jmath_blockDiagQ (A : SL(2, ℤ)) : jmath (blockDiagQ A) = blockDiag (sigmaSL A) := by
  have hinv : (blockDiagQ A)⁻¹ = blockDiagQ A⁻¹ :=
    inv_eq_of_mul_eq_one_right (by rw [← blockDiagQ_mul, mul_inv_cancel, blockDiagQ_one])
  apply Subtype.ext
  rw [coe_jmath, hinv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rt, blockDiagQ, blockDiag, sigmaSL, Fin.rev, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two]

end TernaryPeriodPolynomials.Argument.EisensteinDual
