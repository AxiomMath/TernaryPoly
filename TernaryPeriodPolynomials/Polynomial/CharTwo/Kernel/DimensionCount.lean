module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GeomCount
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.GradedCount
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DicksonWeights

@[expose] public section





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open PowerSeries

/-- **Dimension-count step (a).** `P`'s `k`-th coefficient as an indicator sum over `Fin 28`. -/
theorem coeff_P_eq_sum (k : ℕ) :
    PowerSeries.coeff k P = ∑ m : Fin 28, (if k = stdDeg m then (1 : ℤ) else 0) := by
  simp [P, map_sum, PowerSeries.coeff_X_pow]

/-- **Dimension-count step (b).** `coeff n (geom 1 * geom 2 * geom 3)` as a `Fin 28`-indexed sum
of (possibly shifted) `geom 4 * geom 6 * geom 7` coefficients, one term per `m` with `stdDeg m ≤ n`
(the rest contributing `0`). This is the `PowerSeries`-level form of the dimension count needed for
Ψ_d's finrank equality. -/
theorem coeff_geom123_eq_sum (n : ℕ) :
    PowerSeries.coeff n (geom 1 * geom 2 * geom 3) =
      ∑ m : Fin 28, (if stdDeg m ≤ n then
        PowerSeries.coeff (n - stdDeg m) (geom 4 * geom 6 * geom 7) else 0) := by
  rw [geom123_eq_P_mul_geom467, coeff_mul_range]
  have hstep : ∀ k ∈ Finset.range (n + 1),
      PowerSeries.coeff k P * PowerSeries.coeff (n - k) (geom 4 * geom 6 * geom 7) =
        ∑ m : Fin 28, (if k = stdDeg m then
          PowerSeries.coeff (n - k) (geom 4 * geom 6 * geom 7) else 0) := by
    intro k _
    rw [coeff_P_eq_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by split_ifs <;> simp)
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.sum_ite_eq' (Finset.range (n + 1)) (stdDeg m)
    (fun k => PowerSeries.coeff (n - k) (geom 4 * geom 6 * geom 7))]
  simp [Finset.mem_range]

/-- **Dimension-count step (c).** The `Nat.card` form of (b): the number of weight-`stdWeight`
exponent vectors of total weight `n` equals the sum, over `m : Fin 28` with `stdDeg m ≤ n`, of the
number of weight-`![4,6,7]` exponent vectors of total weight `n - stdDeg m`. -/
theorem card_weight_stdWeight_eq_sum (n : ℕ) :
    Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight stdWeight d = n} =
      ∑ m : Fin 28, (if stdDeg m ≤ n then
        Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight (![4, 6, 7] : Fin 3 → ℕ) d = n - stdDeg m}
      else 0) := by
  have h1 : (Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight stdWeight d = n} : ℤ) =
      PowerSeries.coeff n (geom 1 * geom 2 * geom 3) := by
    simpa [stdWeight] using card_weight_eq_coeff stdWeight n (by decide) (by decide) (by decide)
  have h2 : PowerSeries.coeff n (geom 1 * geom 2 * geom 3) =
      ∑ m : Fin 28, (if stdDeg m ≤ n then
        (Nat.card {d : Fin 3 →₀ ℕ | Finsupp.weight (![4, 6, 7] : Fin 3 → ℕ) d = n - stdDeg m} : ℤ)
      else 0) := by
    rw [coeff_geom123_eq_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    split_ifs with h
    · exact (card_weight_eq_coeff (![4, 6, 7] : Fin 3 → ℕ) (n - stdDeg m)
        (by decide) (by decide) (by decide)).symm
    · rfl
  have h3 := h1.trans h2
  exact_mod_cast h3

/-- **Dimension-count step (d), capstone.** The matching `Module.finrank` equality for the
weighted-homogeneous submodules themselves, in sum-over-subtype form — exactly the shape
`Module.finrank_pi_fintype` will produce for Ψ_d's domain. -/
theorem finrank_weightedHomogeneousSubmodule_stdWeight_eq_sum (n : ℕ) :
    Module.finrank (ZMod 2) (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight n) =
      ∑ m : {m : Fin 28 // stdDeg m ≤ n}, Module.finrank (ZMod 2)
        (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
          (n - stdDeg m.1)) := by
  have hsub : (∑ m : {m : Fin 28 // stdDeg m ≤ n}, Module.finrank (ZMod 2)
        (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
          (n - stdDeg m.1))) =
      ∑ m : Fin 28, (if stdDeg m ≤ n then Module.finrank (ZMod 2)
        (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
          (n - stdDeg m)) else 0) := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun m : Fin 28 => stdDeg m ≤ n)) (by simp)
      (fun m => Module.finrank (ZMod 2) (MvPolynomial.weightedHomogeneousSubmodule (ZMod 2)
        (![4, 6, 7] : Fin 3 → ℕ) (n - stdDeg m)))]
    exact Finset.sum_filter (fun m : Fin 28 => stdDeg m ≤ n) _
  rw [finrank_weightedHomogeneousSubmodule stdWeight (by decide) n, card_weight_stdWeight_eq_sum,
    hsub]
  exact Finset.sum_congr rfl (fun m _ => by
    split_ifs with h
    · exact (finrank_weightedHomogeneousSubmodule (![4, 6, 7] : Fin 3 → ℕ) (by decide)
        (n - stdDeg m)).symm
    · rfl)

end TernaryPeriodPolynomials.Argument.CharTwoKernel
