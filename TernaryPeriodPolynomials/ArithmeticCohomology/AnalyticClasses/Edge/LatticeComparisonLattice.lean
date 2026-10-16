module

public import TernaryPeriodPolynomials.ArithmeticCohomology.AnalyticClasses.DerivativeEdge
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Radical.LatticePairs
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.AdditiveCocycleDifferentiation

@[expose] public section


/-!
# Lattice values of differentiable crossed homomorphisms of the real lower radical

Let `g : ℝ² → Sym^n` be a crossed homomorphism of the real lower radical,
`g(Y + Y') = g(Y) + ρ(Y) g(Y')`, all of whose scalar tests are differentiable at `0`, and let
`wᵢ` be its derivative at `0` in the direction `eᵢ`. Along an axis, `ρ(s eᵢ) = exp(s Dᵢ)` with
`Dᵢ = lowerShear n i`, so `g(s eᵢ) = Σₖ s^{k+1} Dᵢ^k wᵢ / (k+1)!`. At the lattice step `s = 3`
this is `Avg(Gᵢ)(3 wᵢ)`, where `Gᵢ = 3 Dᵢ` is the lower radical lattice generator and `Avg` is
the finite exponential average. Hence the lower radical coordinate of the averaged lattice values
of `g` is `3` times the lower radical coordinate of `(w₀, w₁)`. The same coordinate vanishes on
averaged lattice coboundaries `v - exp(Gᵢ) v`, and the rational lattice action is the real action
at `3 ℤ²`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix

namespace TernaryPeriodPolynomials.AnalyticClasses

open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.EdgeControl

attribute [local instance] complexEndRationalAlgebra

variable {n : ℕ}

/-! ### The lower shear and the lattice generator -/

theorem lowerShear_pow_succ (i : Fin 2) : lowerShear n i ^ (n + 1) = 0 := by
  rw [lowerShear, smul_pow,
    homogeneousShearDerivation_power_zero n 2 i.castSucc (Fin.castSucc_ne_last i), smul_zero]

theorem lowerRadicalGenerator_eq_lowerShear (i : Fin 2) :
    lowerRadicalGenerator n i = (3 : ℂ) • lowerShear n i := by
  rw [lowerRadicalGenerator, lowerShear, smul_smul]
  norm_num

/-- The real lower radical at the lattice step acts by the exponential of the lattice generator. -/
theorem coefficient_lowerAxis_three (i : Fin 2) :
    realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd ((3 : ℝ) • Pi.single i 1))) =
      IsNilpotent.exp (lowerRadicalGenerator n i) := by
  apply LinearMap.ext
  intro v
  rw [coefficient_lowerAxis, lowerRadicalGenerator_eq_lowerShear, Complex.ofReal_ofNat]

/-- The rational lower radical lattice acts through the real lower radical at `3 ℤ²`. -/
theorem rationalCoefficient_lowerRadicalLattice (element : RadicalLattice) :
    rationalCoefficientComponent n trivialCharacter (lowerRadicalLattice element) =
      realCoefficientComponent n trivialCharacter (lineRadicalMatrix (Multiplicative.ofAdd
        ![3 * (element.toAdd.1 : ℝ), 3 * (element.toAdd.2 : ℝ)])) := by
  change realCoefficientComponent n trivialCharacter (GeneralLinearGroup.map (algebraMap ℚ ℝ)
    (lowerPlaneUnipotent (3 * (element.toAdd.1 : ℚ)) (3 * (element.toAdd.2 : ℚ)))) = _
  rw [map_lowerPlaneUnipotent]
  congr 2
  all_goals simp

/-- The rational lower radical lattice generators act by exponentials of the lattice
generators. -/
theorem rationalCoefficient_lowerRadicalLattice_generator (i : Fin 2) :
    rationalCoefficientComponent n trivialCharacter
        (lowerRadicalLattice (radicalLatticeGenerator i)) =
      IsNilpotent.exp (lowerRadicalGenerator n i) := by
  fin_cases i
  · exact lowerRadicalLatticeRep_first n
  · exact lowerRadicalLatticeRep_second n

/-! ### Lattice coboundaries -/

theorem lowerRadicalAverageEquiv_symm_exp_sub (i : Fin 2) (v : HomogeneousPoly n) :
    (lowerRadicalAverageEquiv n i).symm (v - IsNilpotent.exp (lowerRadicalGenerator n i) v) =
      -lowerRadicalGenerator n i v := by
  rw [LinearEquiv.symm_apply_eq]
  have difference := nilpotent_difference_apply (lowerRadicalGenerator n i) n
    (lowerRadicalGenerator_power_zero n i) v
  change _ = nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1) _
  rw [map_neg, ← difference, LinearMap.sub_apply, Module.End.one_apply, neg_sub,
    exp_inst_irrel _ Algebra.toModule]

/-- **The lower radical coordinate kills averaged lattice coboundaries.** -/
theorem lowerRadicalCoordinate_exp_coboundary (v : HomogeneousPoly n) :
    lowerRadicalCoordinate n (fun i => (lowerRadicalAverageEquiv n i).symm
      (v - IsNilpotent.exp (lowerRadicalGenerator n i) v)) = 0 := by
  have pair : (fun i => (lowerRadicalAverageEquiv n i).symm
      (v - IsNilpotent.exp (lowerRadicalGenerator n i) v)) =
      (-3 : ℂ) • fun i => lowerShear n i v := by
    funext i
    rw [lowerRadicalAverageEquiv_symm_exp_sub, lowerRadicalGenerator_eq_lowerShear,
      LinearMap.smul_apply, Pi.smul_apply]
    exact (neg_smul (3 : ℂ) _).symm
  rw [pair, map_smul, lowerRadicalCoordinate_lowerShear, smul_zero]

/-- **The lower radical coordinate kills averaged real coboundaries at the lattice step.** -/
theorem lowerRadicalCoordinate_real_coboundary (v : HomogeneousPoly n) :
    lowerRadicalCoordinate n (fun i => (lowerRadicalAverageEquiv n i).symm
      (v - realCoefficientComponent n trivialCharacter
        (lineRadicalMatrix (Multiplicative.ofAdd ((3 : ℝ) • Pi.single i 1))) v)) = 0 := by
  simp_rw [coefficient_lowerAxis_three]
  exact lowerRadicalCoordinate_exp_coboundary v

/-- **The lower radical coordinate kills averaged lattice coboundaries** of the rational lattice
representation. -/
theorem lowerRadicalCoordinate_lattice_coboundary (v : HomogeneousPoly n) :
    lowerRadicalCoordinate n (fun i => (lowerRadicalAverageEquiv n i).symm
      (v - rationalCoefficientComponent n trivialCharacter
        (lowerRadicalLattice (radicalLatticeGenerator i)) v)) = 0 := by
  simp_rw [rationalCoefficient_lowerRadicalLattice_generator]
  exact lowerRadicalCoordinate_exp_coboundary v

/-! ### Differentiable crossed homomorphisms of the real lower radical -/

section CrossedHom

variable {g : (Fin 2 → ℝ) → HomogeneousPoly n}

/-- The derivative at `0` in the direction `eᵢ` of a family of coefficients. -/
def radicalAxisTangent (g : (Fin 2 → ℝ) → HomogeneousPoly n) (i : Fin 2) : HomogeneousPoly n :=
  ∑ j, fderiv ℝ (fun Y => (homogeneousBasis n).coord j (g Y)) 0 (Pi.single i 1) •
    homogeneousBasis n j

theorem hasDerivAt_radicalAxis
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (i : Fin 2) :
    HasDerivAt (fun s : ℝ => functional (g (s • Pi.single i 1)))
      (functional (radicalAxisTangent g i)) 0 := by
  have line : HasDerivAt (fun s : ℝ => s • (Pi.single i 1 : Fin 2 → ℝ)) (Pi.single i 1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i 1 : Fin 2 → ℝ)
  have coordinate (j) : HasDerivAt
      (fun s : ℝ => (homogeneousBasis n).coord j (g (s • Pi.single i 1)))
      (fderiv ℝ (fun Y => (homogeneousBasis n).coord j (g Y)) 0 (Pi.single i 1)) 0 :=
    (differentiable _).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) line (by simp)
  have expand : (fun s : ℝ => functional (g (s • Pi.single i 1))) = fun s =>
      ∑ j, (homogeneousBasis n).coord j (g (s • Pi.single i 1)) *
        functional (homogeneousBasis n j) := by
    funext s
    exact functional_eq_basis_sum functional _
  rw [expand]
  refine (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (coordinate j).mul_const (functional (homogeneousBasis n j)))).congr_deriv ?_
  simp only [radicalAxisTangent, map_sum, map_smul, smul_eq_mul]

theorem crossedHom_zero
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y')) :
    g 0 = 0 := by
  have origin := cocycle 0 0
  rw [add_zero, ofAdd_zero, map_one, map_one, Module.End.one_apply] at origin
  have doubled : g 0 + g 0 = g 0 + 0 := by rw [add_zero]; exact origin.symm
  exact add_left_cancel doubled

theorem hasDerivAt_radicalAxis_orbit
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y'))
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (i : Fin 2) (s : ℝ) :
    HasDerivAt (fun x : ℝ => functional (g (x • Pi.single i 1)))
      (functional (IsNilpotent.exp ((s : ℂ) • lowerShear n i) (radicalAxisTangent g i))) s := by
  set moved := functional ∘ₗ realCoefficientComponent n trivialCharacter
    (lineRadicalMatrix (Multiplicative.ofAdd (s • Pi.single i 1)))
  have nearby : HasDerivAt (fun x : ℝ => functional (g ((s + x) • Pi.single i 1)))
      (moved (radicalAxisTangent g i)) 0 := by
    have translated : (fun x : ℝ => functional (g ((s + x) • Pi.single i 1))) = fun x : ℝ =>
        functional (g (s • Pi.single i 1)) + moved (g (x • Pi.single i 1)) := by
      funext x
      rw [add_smul, cocycle, map_add]
      rfl
    rw [translated]
    exact (hasDerivAt_radicalAxis differentiable moved i).const_add _
  have shifted : HasDerivAt (fun x : ℝ => functional (g ((s + (x - s)) • Pi.single i 1)))
      (moved (radicalAxisTangent g i)) s :=
    HasDerivAt.comp_sub_const s s (by rwa [sub_self])
  simp only [add_sub_cancel] at shifted
  rw [← coefficient_lowerAxis]
  exact shifted

theorem functional_exp_lowerShear (functional : HomogeneousPoly n →ₗ[ℂ] ℂ)
    (v : HomogeneousPoly n) (i : Fin 2) (s : ℝ) :
    functional (IsNilpotent.exp ((s : ℂ) • lowerShear n i) v) =
      finiteExponentialVector (fun k => functional ((lowerShear n i ^ k) v)) (n + 1) s := by
  have nilpotent : ((s : ℂ) • lowerShear n i) ^ (n + 1) = 0 := by
    rw [smul_pow, lowerShear_pow_succ, smul_zero]
  rw [IsNilpotent.exp_eq_sum nilpotent, LinearMap.sum_apply, map_sum, finiteExponentialVector]
  apply Finset.sum_congr rfl
  intro k _
  rw [LinearMap.smul_apply, ← Rat.cast_smul_eq_qsmul ℂ, smul_pow, LinearMap.smul_apply, map_smul,
    map_smul, smul_eq_mul, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- **Along an axis, a differentiable crossed homomorphism is the finite exponential primitive of
its tangent.** -/
theorem functional_radicalAxis
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y'))
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0)
    (functional : HomogeneousPoly n →ₗ[ℂ] ℂ) (i : Fin 2) (s : ℝ) :
    functional (g (s • Pi.single i 1)) = finiteExponentialPrimitive
      (fun k => functional ((lowerShear n i ^ k) (radicalAxisTangent g i))) (n + 1) s := by
  have derivative (x : ℝ) : HasDerivAt (fun x : ℝ => functional (g (x • Pi.single i 1)) -
      finiteExponentialPrimitive
        (fun k => functional ((lowerShear n i ^ k) (radicalAxisTangent g i))) (n + 1) x) 0 x := by
    have actual := hasDerivAt_radicalAxis_orbit cocycle differentiable functional i x
    rw [functional_exp_lowerShear] at actual
    exact (actual.sub (finiteExponentialPrimitive_hasDerivAt
      (fun k => functional ((lowerShear n i ^ k) (radicalAxisTangent g i))) (n + 1) x)).congr_deriv
        (sub_self _)
  have constant := is_const_of_deriv_eq_zero (fun x => (derivative x).differentiableAt)
    (fun x => (derivative x).deriv) s 0
  rw [zero_smul, crossedHom_zero cocycle, map_zero, finiteExponentialPrimitive_zero,
    sub_zero] at constant
  exact sub_eq_zero.mp constant

/-- The value of a differentiable crossed homomorphism at the lattice step of an axis. -/
theorem radicalAxis_three
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y'))
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0) (i : Fin 2) :
    g ((3 : ℝ) • Pi.single i 1) = nilpotentExponentialAverage (lowerRadicalGenerator n i) (n + 1)
      ((3 : ℂ) • radicalAxisTangent g i) := by
  apply (homogeneousBasis n).ext_elem
  intro j
  rw [← Module.Basis.coord_apply, ← Module.Basis.coord_apply,
    functional_radicalAxis cocycle differentiable, finiteExponentialPrimitive,
    nilpotentExponentialAverage, LinearMap.sum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [rationalEnd_smul_apply]
  rw [lowerRadicalGenerator_eq_lowerShear, smul_pow, LinearMap.smul_apply]
  simp only [map_smul, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- The averaged lattice value of a differentiable crossed homomorphism along an axis is `3` times
its tangent. -/
theorem lowerRadicalAverageEquiv_symm_radicalAxis
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y'))
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0) (i : Fin 2) :
    (lowerRadicalAverageEquiv n i).symm (g ((3 : ℝ) • Pi.single i 1)) =
      (3 : ℂ) • radicalAxisTangent g i := by
  rw [LinearEquiv.symm_apply_eq, radicalAxis_three cocycle differentiable i]
  rfl

/-- **The lattice coordinate of a differentiable crossed homomorphism of the real lower radical
is `3` times the lower radical coordinate of its tangent.** -/
theorem lowerRadicalCoordinate_radicalAxis
    (cocycle : ∀ Y Y', g (Y + Y') = g Y + realCoefficientComponent n trivialCharacter
      (lineRadicalMatrix (Multiplicative.ofAdd Y)) (g Y'))
    (differentiable : ∀ functional : HomogeneousPoly n →ₗ[ℂ] ℂ,
      DifferentiableAt ℝ (fun Y => functional (g Y)) 0) :
    lowerRadicalCoordinate n
        (fun i => (lowerRadicalAverageEquiv n i).symm (g ((3 : ℝ) • Pi.single i 1))) =
      (3 : ℂ) • lowerRadicalCoordinate n (radicalAxisTangent g) := by
  simp_rw [lowerRadicalAverageEquiv_symm_radicalAxis cocycle differentiable]
  rw [← map_smul]
  rfl

end CrossedHom

end TernaryPeriodPolynomials.AnalyticClasses
