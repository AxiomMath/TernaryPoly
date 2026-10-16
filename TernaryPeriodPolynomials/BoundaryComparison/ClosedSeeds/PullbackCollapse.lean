module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviRowContraction
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.PullbackReduce
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.LeviAlgebra

@[expose] public section


/-! Clause (iii) of Lemma C.3 (`ar:lem:seed`): collapsing `formPullback`'s `4`-term output
(`PullbackReduce.lean`) further, using `seedForm`'s own bracket proportionality (every nonzero
`seedForm n h q a b` is a fixed complex multiple of `seedForm n h q 0 2`) and the generic row
contractions (`LeviRowContraction.lean`), down to a single scalar identity. Feeds
`TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- If the bracket factor of `seedForm n h q a b` is `c` times the bracket factor of
`seedForm n h q a' b'`, then `seedForm n h q a b` itself is `C c` times `seedForm n h q a' b'`. -/
theorem seedForm_eq_const_mul (n : ℕ) (h : ℂ → ℂ) (q : Fin 5 → ℝ) (a b a' b' : Fin 5) (c : ℂ)
    (hc : seedBeta q a * seedDTau b - seedBeta q b * seedDTau a =
      c * (seedBeta q a' * seedDTau b' - seedBeta q b' * seedDTau a')) :
    seedForm n h q a b = C c * seedForm n h q a' b' := by
  unfold seedForm
  rw [hc]
  have hscalar : h (seedTau q) * (c * (seedBeta q a' * seedDTau b' - seedBeta q b' * seedDTau a')) =
      c * (h (seedTau q) * (seedBeta q a' * seedDTau b' - seedBeta q b' * seedDTau a')) := by
    ring
  rw [hscalar, map_mul, mul_assoc]

/-- The three nonzero `seedForm` entries other than `(0,2)` among the pairs that matter to
`formPullback_seedForm_eq`, each as a fixed multiple of `seedForm n h q 0 2`. -/
theorem seedForm_zero_three (n : ℕ) (h : ℂ → ℂ) (q : Fin 5 → ℝ) :
    seedForm n h q 0 3 = C Complex.I * seedForm n h q 0 2 :=
  seedForm_eq_const_mul n h q 0 3 0 2 Complex.I (by
    simp only [seedBeta, seedDTau, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring)

theorem seedForm_one_two (n : ℕ) (h : ℂ → ℂ) (q : Fin 5 → ℝ) :
    seedForm n h q 1 2 = C (-seedTau q) * seedForm n h q 0 2 :=
  seedForm_eq_const_mul n h q 1 2 0 2 (-seedTau q) (by
    simp only [seedBeta, seedDTau, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    ring)

theorem seedForm_one_three (n : ℕ) (h : ℂ → ℂ) (q : Fin 5 → ℝ) :
    seedForm n h q 1 3 = C (-seedTau q * Complex.I) * seedForm n h q 0 2 :=
  seedForm_eq_const_mul n h q 1 3 0 2 (-seedTau q * Complex.I) (by
    simp only [seedBeta, seedDTau, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    ring)

/-- The row-contraction cross identity: for *every* `i j : Fin 5`, the antisymmetrized product of
row `i`'s `B`-contraction with row `j`'s `D`-contraction (minus the swap) equals
`(A.det)²/(t·δ³)` times `seedForm`'s own bracket factor at `(i, j)`, evaluated at `p` (not at the
Levi-transformed point). -/
theorem leviMap_fderiv_BD_cross (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (ht : t ≠ 0) (i j : Fin 5) :
    (((fderiv ℝ (leviMap A t) p (Pi.single i 1) 0 : ℂ) -
          seedTau (leviMap A t p) * (fderiv ℝ (leviMap A t) p (Pi.single i 1) 1 : ℂ)) *
        ((fderiv ℝ (leviMap A t) p (Pi.single j 1) 2 : ℂ) +
          Complex.I * (fderiv ℝ (leviMap A t) p (Pi.single j 1) 3 : ℂ))) -
      (((fderiv ℝ (leviMap A t) p (Pi.single i 1) 2 : ℂ) +
          Complex.I * (fderiv ℝ (leviMap A t) p (Pi.single i 1) 3 : ℂ)) *
        ((fderiv ℝ (leviMap A t) p (Pi.single j 1) 0 : ℂ) -
          seedTau (leviMap A t p) * (fderiv ℝ (leviMap A t) p (Pi.single j 1) 1 : ℂ))) =
    ((A.det : ℂ) ^ 2 / ((t : ℂ) * ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 3)) *
      (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i) := by
  rw [leviMap_fderiv_B A t p hden ht i, leviMap_fderiv_B A t p hden ht j,
      leviMap_fderiv_D A t p hden i, leviMap_fderiv_D A t p hden j]
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hden' : seedTau p * (A 1 0 : ℂ) + A 1 1 ≠ 0 := by rw [mul_comm]; exact hden
  field_simp [hden, hden']

/-- The raw `4`-term `formPullback_seedForm_eq` minor combination, re-associated into the
`B`/`D`-cross product form that `leviMap_fderiv_BD_cross` computes. Pure algebra: no hypotheses
beyond the shapes themselves. -/
theorem formPullback_minor_regroup (Φ : (Fin 5 → ℝ) → (Fin 5 → ℝ)) (p : Fin 5 → ℝ) (i j : Fin 5) :
    ((fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 2 -
        fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 0 : ℝ) : ℂ) +
      Complex.I * ((fderiv ℝ Φ p (Pi.single i 1) 0 * fderiv ℝ Φ p (Pi.single j 1) 3 -
          fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 0 : ℝ) : ℂ) -
      seedTau (Φ p) * ((fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 2 -
          fderiv ℝ Φ p (Pi.single i 1) 2 * fderiv ℝ Φ p (Pi.single j 1) 1 : ℝ) : ℂ) -
      seedTau (Φ p) * Complex.I * ((fderiv ℝ Φ p (Pi.single i 1) 1 * fderiv ℝ Φ p (Pi.single j 1) 3 -
          fderiv ℝ Φ p (Pi.single i 1) 3 * fderiv ℝ Φ p (Pi.single j 1) 1 : ℝ) : ℂ) =
    (((fderiv ℝ Φ p (Pi.single i 1) 0 : ℂ) -
          seedTau (Φ p) * (fderiv ℝ Φ p (Pi.single i 1) 1 : ℂ)) *
        ((fderiv ℝ Φ p (Pi.single j 1) 2 : ℂ) +
          Complex.I * (fderiv ℝ Φ p (Pi.single j 1) 3 : ℂ))) -
      (((fderiv ℝ Φ p (Pi.single i 1) 2 : ℂ) +
          Complex.I * (fderiv ℝ Φ p (Pi.single i 1) 3 : ℂ)) *
        ((fderiv ℝ Φ p (Pi.single j 1) 0 : ℂ) -
          seedTau (Φ p) * (fderiv ℝ Φ p (Pi.single j 1) 1 : ℂ))) := by
  push_cast
  ring

/-- Clause (iii)'s pullback collapses to a single scalar multiple of `seedForm n h q 0 2`
(`q := leviMap A t p`), with scalar `(A.det)²/(t·δ³)` times `seedForm`'s own bracket factor
`seedBeta p i * seedDTau j - seedBeta p j * seedDTau i`, evaluated at `p` (not `q`). -/
theorem formPullback_leviMap_seedForm_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (t : ℝ) (p : Fin 5 → ℝ)
    (hden : (A 1 0 : ℂ) * seedTau p + A 1 1 ≠ 0) (ht : t ≠ 0) (n : ℕ) (h : ℂ → ℂ) (i j : Fin 5) :
    formPullback (leviMap A t) (seedForm n h) p i j =
      C (((A.det : ℂ) ^ 2 / ((t : ℂ) * ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 3)) *
          (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i)) *
        seedForm n h (leviMap A t p) 0 2 := by
  rw [formPullback_seedForm_eq (leviMap A t) n h p i j,
      seedForm_zero_three n h (leviMap A t p),
      seedForm_one_two n h (leviMap A t p),
      seedForm_one_three n h (leviMap A t p)]
  have hscalar := (formPullback_minor_regroup (leviMap A t) p i j).trans
    (leviMap_fderiv_BD_cross A t p hden ht i j)
  have key :
      (C ((fderiv ℝ (leviMap A t) p (Pi.single i 1) 0 *
              fderiv ℝ (leviMap A t) p (Pi.single j 1) 2 -
            fderiv ℝ (leviMap A t) p (Pi.single i 1) 2 *
              fderiv ℝ (leviMap A t) p (Pi.single j 1) 0 : ℝ) : ℂ) :
          MvPolynomial (Fin 3) ℂ) +
        C ((fderiv ℝ (leviMap A t) p (Pi.single i 1) 0 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 3 -
              fderiv ℝ (leviMap A t) p (Pi.single i 1) 3 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 0 : ℝ) : ℂ) * C Complex.I +
        C ((fderiv ℝ (leviMap A t) p (Pi.single i 1) 1 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 2 -
              fderiv ℝ (leviMap A t) p (Pi.single i 1) 2 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 1 : ℝ) : ℂ) *
            C (-seedTau (leviMap A t p)) +
        C ((fderiv ℝ (leviMap A t) p (Pi.single i 1) 1 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 3 -
              fderiv ℝ (leviMap A t) p (Pi.single i 1) 3 *
                fderiv ℝ (leviMap A t) p (Pi.single j 1) 1 : ℝ) : ℂ) *
            C (-seedTau (leviMap A t p) * Complex.I) =
      C (((A.det : ℂ) ^ 2 / ((t : ℂ) * ((A 1 0 : ℂ) * seedTau p + A 1 1) ^ 3)) *
          (seedBeta p i * seedDTau j - seedBeta p j * seedDTau i)) := by
    rw [← hscalar]
    simp only [map_add, map_sub, map_mul, map_neg]
    ring
  linear_combination seedForm n h (leviMap A t p) 0 2 * key

end TernaryPeriodPolynomials.Argument
