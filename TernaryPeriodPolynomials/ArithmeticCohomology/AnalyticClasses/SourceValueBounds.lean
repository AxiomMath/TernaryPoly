module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.Good.LineUniformDecay
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteCuspIntegral

@[expose] public section


/-!
# Uniform decay of the actual source cusp values along the good line

Every linear functional on the ternary coefficient space is a finite combination of monomial
coefficients. Each monomial coefficient of a source cocycle is a plane-induced section at the
cohomological point, so the uniform decay of `GoodLineUniformDecay` applies to every scalar test
of the source cusp values, and hence to the good-line mixed cusp values entering the standard
integral.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix MvPolynomial

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.PlaneEisensteinContinuation
open TernaryPeriodPolynomials.SphericalDetection.Helpers

variable {n : ℕ}

/-- The degree-`n` monomials of three variables. -/
def degreeMonomials (n : ℕ) : Finset (Fin 3 →₀ ℕ) := Finset.finsuppAntidiag Finset.univ n

/-- The homogeneous projection of a monomial, as an element of `HomogeneousPoly n`. -/
def monomialVector (n : ℕ) (m : Fin 3 →₀ ℕ) : HomogeneousPoly n :=
  ⟨homogeneousComponent n (monomial m 1), homogeneousComponent_mem n _⟩

theorem support_subset_degreeMonomials (p : HomogeneousPoly n) :
    p.val.support ⊆ degreeMonomials n := by
  intro m hm
  have hhom : p.val.IsHomogeneous n := (mem_homogeneousSubmodule n p.val).mp p.property
  have hdeg : Finsupp.weight 1 m = n := hhom (mem_support_iff.mp hm)
  rw [degreeMonomials, Finset.mem_finsuppAntidiag]
  refine ⟨?_, Finset.subset_univ _⟩
  have hw : Finsupp.weight (1 : Fin 3 → ℕ) m = Finsupp.degree m := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [← hdeg, hw, Finsupp.degree_eq_sum]

theorem monomialVector_val {m : Fin 3 →₀ ℕ} (hm : m ∈ degreeMonomials n) :
    (monomialVector n m).val = monomial m 1 := by
  rw [degreeMonomials, Finset.mem_finsuppAntidiag] at hm
  have hdeg : Finsupp.degree m = n := by
    rw [Finsupp.degree_eq_sum]; exact hm.1
  have hmem : (monomial m (1 : ℂ)) ∈ homogeneousSubmodule (Fin 3) ℂ n :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_monomial _ hdeg)
  change homogeneousComponent n (monomial m 1) = monomial m 1
  rw [homogeneousComponent_of_mem hmem, ite_eq_left rfl]

/-- A homogeneous polynomial is the sum of its monomial terms. -/
theorem homogeneous_eq_sum (p : HomogeneousPoly n) :
    p = ∑ m ∈ degreeMonomials n, p.val.coeff m • monomialVector n m := by
  apply Subtype.ext
  rw [Submodule.coe_sum]
  conv_lhs => rw [p.val.as_sum]
  rw [Finset.sum_subset (support_subset_degreeMonomials p)]
  · apply Finset.sum_congr rfl
    intro m hm
    rw [Submodule.coe_smul, monomialVector_val hm, smul_monomial, smul_eq_mul, mul_one]
  · intro m _ hm
    rw [notMem_support_iff.mp hm, monomial_zero]

/-- Every linear functional is a finite combination of monomial coefficients. -/
theorem functional_eq_sum_coeff (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (p : HomogeneousPoly n) :
    functional p = ∑ m ∈ degreeMonomials n, p.val.coeff m * functional (monomialVector n m) := by
  conv_lhs => rw [homogeneous_eq_sum p]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

theorem norm_functional_le (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (p : HomogeneousPoly n) :
    ‖functional p‖ ≤ ∑ m ∈ degreeMonomials n, ‖functional (monomialVector n m)‖ * ‖p.val.coeff m‖ := by
  rw [functional_eq_sum_coeff functional p]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro m _
  rw [norm_mul, mul_comm]

/-- Monomial coefficients of the source cusp values at `g(u)` decay uniformly. -/
theorem sourceCuspidalValues_coeff_decay (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (m : Fin 3 →₀ ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (argument : BinaryAdelicGL),
      ‖((sourcePlaneCuspidalValues data source cocycle vertices
        (atInfinity (standardGoodLineRealArgument u))).val argument).val.coeff m‖ ≤
        (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  have hf := (cocycle.1 vertices m)
  obtain ⟨C, hC0, hC⟩ := goodLine_cuspSupNorm_decay data hf
  refine ⟨C, hC0, fun u argument => ?_⟩
  have hone : inMaximalCompact (1 : AdelicGL) := by
    refine ⟨by simp, ⟨1, by simp⟩⟩
  have bound := hC u 1 hone
  rw [mul_one] at bound
  have realized := CuspVectors.realize_planeCuspVector hf
    (atInfinity (standardGoodLineRealArgument u)) argument
  have value : ((sourcePlaneCuspidalValues data source cocycle vertices
      (atInfinity (standardGoodLineRealArgument u))).val argument).val.coeff m =
      data.cusp.realize (CuspVectors.planeCuspVector hf
        (atInfinity (standardGoodLineRealArgument u))) argument := by
    rw [realized, binaryInductionExponent_plane_endpoint]
    simp [sourcePlaneCuspidalValues]
  rw [value]
  exact (CuspSupNorm.realize_le_cuspSupNorm _ argument).trans bound

/-- Every scalar test of the source cusp values at `g(u)` decays uniformly. -/
theorem sourceCuspidalValues_functional_decay (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (vertices : Fin 3 → RealGL3)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (argument : BinaryAdelicGL),
      ‖functional ((sourcePlaneCuspidalValues data source cocycle vertices
        (atInfinity (standardGoodLineRealArgument u))).val argument)‖ ≤
        (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  choose C hC0 hC using fun m => sourceCuspidalValues_coeff_decay data source cocycle vertices m
  refine ⟨∑ m ∈ degreeMonomials n, ‖functional (monomialVector n m)‖ * C m,
    Finset.sum_nonneg (fun m _ => mul_nonneg (norm_nonneg _) (hC0 m)), fun u argument => ?_⟩
  refine (norm_functional_le functional _).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m _
  calc ‖functional (monomialVector n m)‖ * ‖((sourcePlaneCuspidalValues data source cocycle
        vertices (atInfinity (standardGoodLineRealArgument u))).val argument).val.coeff m‖ ≤
      ‖functional (monomialVector n m)‖ * ((1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C m) :=
        mul_le_mul_of_nonneg_left (hC m u argument) (norm_nonneg _)
    _ = _ := by ring

/-- **Uniform decay of the mixed good-line cusp values.** -/
theorem mixedCuspidalValues_decay (data : InducingData n) (source : SourceCochain n)
    (cocycle : IsSourceCocycle data .plane source) (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (functional : Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℝ × ℝ) (argument : BinaryAdelicGL),
      ‖data.cusp.realize (cuspidalTensorFunctional data.cusp functional
        (goodLineMixedCuspidalValues data source cocycle matrix
          (atInfinity (standardGoodLineRealArgument u)))) argument‖ ≤
        (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4)) * C := by
  let L0 := functional.comp (lowerRadicalLatticeContribution n 0)
  let L1 := functional.comp (lowerRadicalLatticeContribution n 1)
  let x1 := goodLineRealVertices (goodLineLeviSection matrix,
    goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeFirst))
  let x2 := goodLineRealVertices (goodLineRadicalInclusion radicalLatticeFirst, goodLineLeviSection matrix)
  let x3 := goodLineRealVertices (goodLineLeviSection matrix,
    goodLineRadicalInclusion (lowerLeviLatticeInput matrix radicalLatticeSecond))
  let x4 := goodLineRealVertices (goodLineRadicalInclusion radicalLatticeSecond, goodLineLeviSection matrix)
  obtain ⟨C1, h1, b1⟩ := sourceCuspidalValues_functional_decay data source cocycle x1 L0
  obtain ⟨C2, h2, b2⟩ := sourceCuspidalValues_functional_decay data source cocycle x2 L0
  obtain ⟨C3, h3, b3⟩ := sourceCuspidalValues_functional_decay data source cocycle x3 L1
  obtain ⟨C4, h4, b4⟩ := sourceCuspidalValues_functional_decay data source cocycle x4 L1
  refine ⟨C1 + C2 + C3 + C4, by positivity, fun u argument => ?_⟩
  rw [cuspidalTensorFunctional_realize, goodLineMixedCuspidalValues_apply,
    goodLineMixedRealCoordinate_contributions]
  simp only [map_add, map_sub]
  set D := (1 + u.1 ^ 2 + u.2 ^ 2) ^ (-(((n : ℝ) + 3) / 4))
  have e1 := b1 u argument
  have e2 := b2 u argument
  have e3 := b3 u argument
  have e4 := b4 u argument
  simp only [L0, L1, LinearMap.comp_apply] at e1 e2 e3 e4
  calc _ ≤ ‖functional (lowerRadicalLatticeContribution n 0 ((sourcePlaneCuspidalValues data source
          cocycle x1 (atInfinity (standardGoodLineRealArgument u))).val argument)) -
        functional (lowerRadicalLatticeContribution n 0 ((sourcePlaneCuspidalValues data source
          cocycle x2 (atInfinity (standardGoodLineRealArgument u))).val argument))‖ +
        ‖functional (lowerRadicalLatticeContribution n 1 ((sourcePlaneCuspidalValues data source
          cocycle x3 (atInfinity (standardGoodLineRealArgument u))).val argument)) -
        functional (lowerRadicalLatticeContribution n 1 ((sourcePlaneCuspidalValues data source
          cocycle x4 (atInfinity (standardGoodLineRealArgument u))).val argument))‖ := norm_add_le _ _
    _ ≤ (D * C1 + D * C2) + (D * C3 + D * C4) :=
        add_le_add ((norm_sub_le _ _).trans (add_le_add e1 e2))
          ((norm_sub_le _ _).trans (add_le_add e3 e4))
    _ = D * (C1 + C2 + C3 + C4) := by ring

end TernaryPeriodPolynomials.AnalyticClasses
