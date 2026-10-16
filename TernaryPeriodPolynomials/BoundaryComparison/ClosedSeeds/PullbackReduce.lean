module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviJacobianValues

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the general reduction of `formPullback`'s
`Fin 5 × Fin 5` double sum against `seedForm`, valid for *any* map `Φ`, down to its `4` genuinely
nontrivial terms (the other `21` of the `25` vanish by `seedForm`'s sparsity/antisymmetry,
`seedForm_trivial_pairs`/`seedForm_swap` from `LeviAlgebra.lean`). Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

theorem formPullback_seedForm_eq (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (n : ℕ) (h : ℂ → ℂ)
    (p : Fin 5 → ℝ) (i j : Fin 5) :
    formPullback Φ (seedForm n h) p i j =
      C ((fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 2 -
          fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 0 : ℝ) : ℂ) *
        seedForm n h (Φ p) 0 2 +
      C ((fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 3 -
          fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 0 : ℝ) : ℂ) *
        seedForm n h (Φ p) 0 3 +
      C ((fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 2 -
          fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 1 : ℝ) : ℂ) *
        seedForm n h (Φ p) 1 2 +
      C ((fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 3 -
          fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 1 : ℝ) : ℂ) *
        seedForm n h (Φ p) 1 3 := by
  obtain ⟨t00, t01, t04, t10, t11, t14, t22, t23, t24, t32, t33, t34, t40, t41, t42, t43, t44⟩ :=
    seedForm_trivial_pairs n h (Φ p)
  have s02 := seedForm_swap n h (Φ p) 0 2
  have s03 := seedForm_swap n h (Φ p) 0 3
  have s12 := seedForm_swap n h (Φ p) 1 2
  have s13 := seedForm_swap n h (Φ p) 1 3


  have combine : ∀ x y : ℝ, (C ((x : ℂ)) : MvPolynomial (Fin 3) ℂ) - C ((y : ℂ)) =
      C (((x - y : ℝ) : ℂ)) := by
    intro x y
    rw [← map_sub]
    norm_cast
  unfold formPullback
  simp only [Fin.sum_univ_five, t00, t01, t04, t10, t11, t14, t22, t23, t24, t32, t33, t34,
    t40, t41, t42, t43, t44, mul_zero, add_zero, zero_add, s02, s03, s12, s13, mul_neg]
  linear_combination
    seedForm n h (Φ p) 0 2 *
        combine (fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 2)
          (fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 0) +
      seedForm n h (Φ p) 0 3 *
        combine (fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 3)
          (fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 0) +
      seedForm n h (Φ p) 1 2 *
        combine (fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 2)
          (fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 1) +
      seedForm n h (Φ p) 1 3 *
        combine (fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 3)
          (fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 1)
