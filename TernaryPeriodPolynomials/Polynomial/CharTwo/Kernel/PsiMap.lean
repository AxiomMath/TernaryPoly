module

public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.DimensionCount
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.ModuleFiniteWeighted
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.HomogeneousExpand
public import TernaryPeriodPolynomials.Polynomial.CharTwo.Kernel.AevalWeighted
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.Finiteness.Lattice

@[expose] public section





noncomputable section

namespace TernaryPeriodPolynomials.Argument.CharTwoKernel

open MvPolynomial
open TernaryPoly.DicksonQuotient (Poly invariantEval standardMonomial d4 d6 d7)

/-- **Ψ_d, prerequisite (a).** `invariantEval` sends a `![4,6,7]`-weighted-homogeneous polynomial
of degree `e` to a `stdWeight`-weighted-homogeneous polynomial of the *same* degree `e`. -/
theorem isWeightedHomogeneous_invariantEval {q : Poly} {e : ℕ}
    (hq : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) q e) :
    IsWeightedHomogeneous stdWeight (invariantEval q) e := by
  have hhom : ∀ j : Fin 3,
      IsWeightedHomogeneous stdWeight ((![d4, d6, d7] : Fin 3 → Poly) j)
        ((![4, 6, 7] : Fin 3 → ℕ) j) := by
    intro j
    fin_cases j
    · simpa using isWeightedHomogeneous_d4
    · simpa using isWeightedHomogeneous_d6
    · simpa using isWeightedHomogeneous_d7
  have h := isWeightedHomogeneous_aeval (![4, 6, 7] : Fin 3 → ℕ) stdWeight
    (![d4, d6, d7] : Fin 3 → Poly) hhom hq
  rwa [show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl]

/-- **Ψ_d, prerequisite (b).** For `i : Fin 28` with `stdDeg i ≤ d` and `q` a `![4,6,7]`-weighted-
homogeneous polynomial of the truncated degree `d - stdDeg i`, the single term
`invariantEval q * standardMonomial i` is `stdWeight`-weighted-homogeneous of degree `d` exactly
(no truncation, since `stdDeg i ≤ d`). -/
theorem isWeightedHomogeneous_term {d : ℕ} {i : Fin 28} (h : stdDeg i ≤ d) {q : Poly}
    (hq : IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) q (d - stdDeg i)) :
    IsWeightedHomogeneous stdWeight (invariantEval q * standardMonomial i) d := by
  have h1 : IsWeightedHomogeneous stdWeight (invariantEval q) (d - stdDeg i) :=
    isWeightedHomogeneous_invariantEval hq
  have h2 := h1.mul (isWeightedHomogeneous_standardMonomial i)
  rwa [Nat.sub_add_cancel h] at h2

/-- **Ψ_d, raw function.** Given, for every `m : Fin 28` with `stdDeg m ≤ d`, a `![4,6,7]`-weighted-
homogeneous coefficient of the matching truncated degree, sum `invariantEval (coefficient) *
standardMonomial m` to get a `stdWeight`-weighted-homogeneous polynomial of degree `d`. -/
def psiFun (d : ℕ)
    (c : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) :
    ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight d) :=
  ⟨∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (c m : Poly) * standardMonomial m.1,
    Submodule.sum_mem _ (fun m _ =>
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        (isWeightedHomogeneous_term m.2
          ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp (c m).2)))⟩

theorem psiFun_add (d : ℕ)
    (c c' : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) :
    psiFun d (c + c') = psiFun d c + psiFun d c' := by
  refine Subtype.ext ?_
  simp only [psiFun, Submodule.coe_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl, map_add, add_mul]

theorem psiFun_smul (d : ℕ) (r : ZMod 2)
    (c : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) :
    psiFun d (r • c) = r • psiFun d c := by
  refine Subtype.ext ?_
  simp only [psiFun, Submodule.coe_smul, Pi.smul_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show invariantEval = aeval (R := ZMod 2) ![d4, d6, d7] from rfl, map_smul, smul_mul_assoc]

/-- **Ψ_d, bundled `LinearMap`.** Domain: one `![4,6,7]`-homogeneous coefficient (of the matching
truncated degree) for every `m : Fin 28` with `stdDeg m ≤ d`. Codomain: the degree-`d`
`stdWeight`-weighted-homogeneous submodule. -/
def psi (d : ℕ) :
    ((m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1))) →ₗ[ZMod 2]
    ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight d) where
  toFun := psiFun d
  map_add' := psiFun_add d
  map_smul' := psiFun_smul d

/-- **Ψ_d, surjectivity.** Every degree-`d` `stdWeight`-weighted-homogeneous polynomial is a Ψ_d
image: expand it via `homogeneous_expand`, then show the terms with `stdDeg i > d` do not
contribute to the degree-`d` component (regardless of their own coefficient, via
`weightedHomogeneousComponent_mul_eq_zero_of_lt`), leaving exactly the sum over
`{m // stdDeg m ≤ d}`. -/
theorem psi_surjective (d : ℕ) : Function.Surjective (psi d) := by
  intro y
  have hyhom : IsWeightedHomogeneous stdWeight (y : Poly) d :=
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp y.2
  obtain ⟨coeff, hcoeffdeg, hcoeffeq⟩ := homogeneous_expand hyhom
  refine ⟨fun m => ⟨coeff m.1,
      (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hcoeffdeg m.1)⟩, ?_⟩
  refine Subtype.ext ?_
  show (∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (coeff m.1) * standardMonomial m.1 : Poly)
    = (y : Poly)
  have hstep : ∀ i : Fin 28, weightedHomogeneousComponent stdWeight d
      (invariantEval (coeff i) * standardMonomial i) =
        (if stdDeg i ≤ d then invariantEval (coeff i) * standardMonomial i else 0) := by
    intro i
    split_ifs with h
    · exact (isWeightedHomogeneous_term h (hcoeffdeg i)).weightedHomogeneousComponent_same
    · exact weightedHomogeneousComponent_mul_eq_zero_of_lt
        (isWeightedHomogeneous_standardMonomial i) (invariantEval (coeff i)) (by omega)
  have hy : (y : Poly) = ∑ i : Fin 28,
      (if stdDeg i ≤ d then invariantEval (coeff i) * standardMonomial i else 0) := by
    rw [hyhom.weightedHomogeneousComponent_same.symm, hcoeffeq, map_sum]
    exact Finset.sum_congr rfl (fun i _ => hstep i)
  rw [hy, ← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun i : Fin 28 => stdDeg i ≤ d)) (by simp)
    (fun i => invariantEval (coeff i) * standardMonomial i)).symm

/-- **Ψ_d, injectivity.** Via matching finranks (`DimensionCount.lean`'s
`finrank_weightedHomogeneousSubmodule_stdWeight_eq_sum` plus `Module.finrank_pi_fintype`) and
`psi_surjective`. -/
theorem psi_injective (d : ℕ) : Function.Injective (psi d) := by
  have hfree : ∀ i : {m : Fin 28 // stdDeg m ≤ d},
      Module.Free (ZMod 2)
        ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
          (d - stdDeg i.1)) :=
    fun i => Module.Free.of_divisionRing (ZMod 2) _
  have hfin : Module.finrank (ZMod 2)
      ((m : {m : Fin 28 // stdDeg m ≤ d}) →
        ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
          (d - stdDeg m.1))) =
      Module.finrank (ZMod 2) (↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) stdWeight d)) := by
    rw [Module.finrank_pi_fintype (ZMod 2), finrank_weightedHomogeneousSubmodule_stdWeight_eq_sum]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mpr (psi_surjective d)

/-- **Ψ_d, elementary injectivity (standalone, un-bundled form for downstream use).** If two
families of `![4,6,7]`-weighted-homogeneous "coefficients" (one per `m : Fin 28` with
`stdDeg m ≤ d`, of the matching truncated degree) produce the same `Σ invariantEval(·) *
standardMonomial(·)` sum, the two families agree pointwise. This is the form Lemma A's
per-degree pivot argument will actually consume. -/
theorem psi_injective_elementary (d : ℕ) (q q' : {m : Fin 28 // stdDeg m ≤ d} → Poly)
    (hq : ∀ m, IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (q m) (d - stdDeg m.1))
    (hq' : ∀ m, IsWeightedHomogeneous (![4, 6, 7] : Fin 3 → ℕ) (q' m) (d - stdDeg m.1))
    (heq : ∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (q m) * standardMonomial m.1 =
           ∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (q' m) * standardMonomial m.1)
    (m₀ : {m : Fin 28 // stdDeg m ≤ d}) : q m₀ = q' m₀ := by
  let c : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1)) :=
    fun m => ⟨q m, (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hq m)⟩
  let c' : (m : {m : Fin 28 // stdDeg m ≤ d}) →
      ↥(MvPolynomial.weightedHomogeneousSubmodule (ZMod 2) (![4, 6, 7] : Fin 3 → ℕ)
        (d - stdDeg m.1)) :=
    fun m => ⟨q' m, (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr (hq' m)⟩
  have hceq : (psi d c : Poly) = (psi d c' : Poly) := by
    show (∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (c m : Poly) * standardMonomial m.1 : Poly)
      = ∑ m : {m : Fin 28 // stdDeg m ≤ d}, invariantEval (c' m : Poly) * standardMonomial m.1
    exact heq
  have hcc' : c = c' := psi_injective d (Subtype.ext hceq)
  exact congrArg Subtype.val (congrFun hcc' m₀)

end TernaryPeriodPolynomials.Argument.CharTwoKernel
