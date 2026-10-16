module

public import TernaryPeriodPolynomials.BoundaryComparison.LineSeed.Line.Transform

@[expose] public section


/-!
# The primitives `θ_g` of the defect `g^*η - ρ(g)η` for the line seed (LS6, part 1)

`θ_g(x) = Σ_{k ≤ n} C(n,k)(-1)^{n-k} (v₀(g) G_{k+1}(τ) + v₁(g) G_k(τ)) ρ(g)(Z^k Y^{n-k})` with `G_j' = h z^j`.  Its derivative along `τ` is
`h(τ)(τ v₀ + v₁) ρ(g)(P_τⁿ)` (binomial theorem), the defect of `Ψ` (`LineTransform.defect_poly`).

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial
open scoped ContDiff

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LineSeed

open TernaryPeriodPolynomials.Argument.SeedC3 TernaryPeriodPolynomials.Argument.SeedC3.Psi
open TernaryPeriodPolynomials.Argument.SeedC3.Calc

theorem rho_sum_general {ι : Type*} (M : Matrix (Fin 3) (Fin 3) ℝ) (s : Finset ι) (f : ι → MvPolynomial (Fin 3) ℂ) :
    rho M (∑ i ∈ s, f i) = ∑ i ∈ s, rho M (f i) := by
  unfold rho
  rw [map_sum, Finset.mul_sum]

theorem toPoly_sum_coef {ι : Type*} {n : ℕ} (s : Finset ι) (f : ι → Coef n) :
    Coef.toPoly (∑ i ∈ s, f i) = ∑ i ∈ s, Coef.toPoly (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Coef.toPoly_add, ih]

theorem monoZY_isHomogeneous (n k : ℕ) (hk : k ≤ n) :
    (X 2 ^ k * X 1 ^ (n - k) : MvPolynomial (Fin 3) ℂ).IsHomogeneous n := by
  have := ((isHomogeneous_X ℂ (2 : Fin 3)).pow k).mul ((isHomogeneous_X ℂ (1 : Fin 3)).pow (n - k))
  have e : 1 * k + 1 * (n - k) = n := by omega
  rwa [e] at this

namespace LineData

variable {G : Type} [Group G] (D : LineData G) (h : ℂ → ℂ) (n : ℕ) (Gm : ℕ → ℂ → ℂ)

/-- The coefficient `ρ(g)(Z^k Y^{n-k}) ∈ E_n`. -/
def thetaVec (g : G) (k : ℕ) : Coef n := D.rhoCoef n g (toCoef n (X 2 ^ k * X 1 ^ (n - k)))

theorem toPoly_thetaVec (g : G) {k : ℕ} (hk : k ≤ n) :
    Coef.toPoly (D.thetaVec n g k) = rho (D.lmat g) (X 2 ^ k * X 1 ^ (n - k)) := by
  rw [thetaVec, D.toPoly_rhoCoef, toPoly_toCoef_of_isHomogeneous n (monoZY_isHomogeneous n k hk)]

/-- The scalar `C(n,k)(-1)^{n-k} (v₀ a + v₁ b)`. -/
def thetaScalar (g : G) (k : ℕ) (a b : ℂ) : ℂ :=
  (n.choose k : ℂ) * (-1) ^ (n - k) * ((D.v g 0 : ℂ) * a + (D.v g 1 : ℂ) * b)

/-- `θ_g(x) = Σ_k C(n,k)(-1)^{n-k}(v₀ G_{k+1}(τ) + v₁ G_k(τ)) ρ(g)(Z^k Y^{n-k})`. -/
def thetaFun (g : G) (x : Face) : Coef n :=
  ∑ k ∈ Finset.range (n + 1), D.thetaScalar n g k (Gm (k + 1) (faceTau x)) (Gm k (faceTau x)) • D.thetaVec n g k

theorem toPoly_thetaFun (g : G) (x : Face) :
    Coef.toPoly (D.thetaFun n Gm g x) =
      ∑ k ∈ Finset.range (n + 1),
        C ((n.choose k : ℂ) * (-1) ^ (n - k) *
            ((D.v g 0 : ℂ) * Gm (k + 1) (faceTau x) + (D.v g 1 : ℂ) * Gm k (faceTau x))) *
          rho (D.lmat g) (X 2 ^ k * X 1 ^ (n - k)) := by
  unfold thetaFun
  rw [toPoly_sum_coef]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Coef.toPoly_smul, D.toPoly_thetaVec n g hk']
  rfl

/-- The derivative of `θ_g` in `τ`: `Σ_k C(n,k)(-1)^{n-k}(v₀ h τ^{k+1} + v₁ h τ^k) ρ(g)(Z^k Y^{n-k})`. -/
def thetaDeriv (g : G) (τ : ℂ) : Coef n :=
  ∑ k ∈ Finset.range (n + 1), D.thetaScalar n g k (h τ * τ ^ (k + 1)) (h τ * τ ^ k) • D.thetaVec n g k

/-- **Binomial theorem**: `θ_g'(τ) = h(τ)(τ v₀ + v₁) ρ(g)(P_τⁿ)`. -/
theorem toPoly_thetaDeriv (g : G) (τ : ℂ) :
    Coef.toPoly (D.thetaDeriv h n g τ) =
      C (h τ * (τ * (D.v g 0 : ℂ) + (D.v g 1 : ℂ))) * rho (D.lmat g) (Ppoly τ ^ n) := by
  unfold thetaDeriv
  rw [toPoly_sum_coef]
  have hP : Ppoly τ ^ n = ∑ k ∈ Finset.range (n + 1),
      C ((n.choose k : ℂ) * (-1) ^ (n - k) * τ ^ k) * (X 2 ^ k * X 1 ^ (n - k)) := by
    unfold Ppoly
    rw [sub_eq_add_neg, add_pow]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, neg_pow, ← map_pow]
    simp only [map_mul, map_pow, map_neg, map_one, map_natCast]
    ring
  rw [hP, rho_sum_general, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Coef.toPoly_smul, D.toPoly_thetaVec n g hk', rho_C_mul_general, ← mul_assoc, ← map_mul]
  unfold thetaScalar
  congr 2
  ring

end LineData

end TernaryPeriodPolynomials.Argument.LineSeed
