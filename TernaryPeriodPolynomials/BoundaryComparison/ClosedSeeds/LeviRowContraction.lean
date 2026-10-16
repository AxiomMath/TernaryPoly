module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviJacobianValues

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): the two "row contraction" identities turning each
row `i` of `leviMap A t`'s Jacobian into a single scalar multiple of `seedBeta p i` /
`seedDTau i`, valid for *all* `i : Fin 5` at once (not just the four nontrivial index pairs).
These let `formPullback`'s Jacobian-weighted sum be matched against `seedForm`'s own
`seedBeta`/`seedDTau` bracket without a `25`-way case split on `(i, j)`. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- `z * I` split into its real/imaginary parts, used to recombine `leviMap`'s Möbius-block
Jacobian rows (given as separate real/imaginary components) into one complex scalar. -/
theorem mul_I_eq (z : ℂ) : z * Complex.I = -(z.im : ℂ) + Complex.I * (z.re : ℂ) := by
  apply Complex.ext <;> simp

/-- The `(0,1)`-component contraction of row `i` of `leviMap A t`'s Jacobian: for *every*
`i : Fin 5`, `J(i,0) - τ(Φp)·J(i,1)` equals `(A.det / (t·δ))` times `seedBeta p i`, where
`δ = (A 1 0 : ℂ) * seedTau p + A 1 1` and `Φp = leviMap A t p`. -/
theorem leviMap_fderiv_B (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (ht : t ≠ 0) (i : Fin 5) :
    (fderiv ℝ (leviMap A t) p (Pi.single i 1) 0 : ℂ) -
      seedTau (leviMap A t p) * (fderiv ℝ (leviMap A t) p (Pi.single i 1) 1 : ℂ) =
      ((A.det : ℂ) / ((t : ℂ) * ((A 1 0 : ℂ) * seedTau p + A 1 1))) * seedBeta p i := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hdetval : (A.det : ℂ) = (A 0 0 : ℂ) * A 1 1 - (A 0 1 : ℂ) * A 1 0 := by
    rw [Matrix.det_fin_two]; push_cast; ring



  have hden' : seedTau p * (A 1 0 : ℂ) + A 1 1 ≠ 0 := by rw [mul_comm]; exact hden
  rw [seedTau_leviMap]
  fin_cases i
  · simp [leviMap_fderiv_row0 A t p hden, seedBeta]
    field_simp [hden, hden']
    rw [hdetval]; ring
  · simp [leviMap_fderiv_row1 A t p hden, seedBeta]
    field_simp [hden, hden']
    rw [hdetval]; ring
  · simp [leviMap_fderiv_row2 A t p hden, seedBeta]
  · simp [leviMap_fderiv_row3 A t p hden, seedBeta]
  · simp [leviMap_fderiv_row4 A t p hden, seedBeta]

/-- The `(2,3)`-component contraction of row `i` of `leviMap A t`'s Jacobian: for *every*
`i : Fin 5`, `J(i,2) + I·J(i,3)` equals `(A.det / δ²)` times `seedDTau i`. -/
theorem leviMap_fderiv_D (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (i : Fin 5) :
    (fderiv ℝ (leviMap A t) p (Pi.single i 1) 2 : ℂ) +
      Complex.I * (fderiv ℝ (leviMap A t) p (Pi.single i 1) 3 : ℂ) =
      ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2) * seedDTau i := by
  fin_cases i
  · simp [leviMap_fderiv_row0 A t p hden, seedDTau]
  · simp [leviMap_fderiv_row1 A t p hden, seedDTau]
  · simp [leviMap_fderiv_row2 A t p hden, seedDTau]
    linear_combination Complex.re_add_im ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)
  · simp [leviMap_fderiv_row3 A t p hden, seedDTau]


    linear_combination -mul_I_eq ((A.det : ℂ) / ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 2)
  · simp [leviMap_fderiv_row4 A t p hden, seedDTau]

end TernaryPeriodPolynomials.Argument
