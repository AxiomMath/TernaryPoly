module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Hecke.Multiplicativity
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.HermiteCount

@[expose] public section


/-!
# The lattice Hecke operator at level one: obligation (b)

Formalized by Claude Haiku 5.5.

For a weight `k : ℤ` and `n ≥ 1`, the lattice operator on functions `ℍ → ℂ` is the sum over the
Hermite column representatives `(a, b, d)` of index `n` (`hnfData n`: `a d = n`, `a ≥ 1`, `0 ≤ b < d`):

  `latticeOp k n F z = ∑_{(a,b,d)} (a d)^{k-1} d^{-k} F((a z + b)/d)`.

The weight `(a d)^{k-1} d^{-k}` is the classical one (Serre's normalization of `T_n`). With it,
`latticeOp k p` at prime `p` is exactly the prime Hecke sum of `HasPrimeHeckeRelations`: the dilate
`(p, 0, 1)` has weight `p^{k-1}` and the translates `(1, j, p)` have weight `p^{-1}`.

Proved here: `latticeOp_one` (the prime-level identity) and `hasPrimeHeckeRelations_iff_latticeOp`.
Not proved here: the composition law `T_p ∘ T_{p^r}` and the eigenvalue identity at `p^r`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator

open Finset Matrix TernaryPeriodPolynomials.SphericalDetection.Helpers

/-- The real matrix `[[a, b], [0, d]]` attached to a Hermite triple `(a, b, d)`. -/
def hnfMat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(t.1 : ℝ), (t.2.1 : ℝ); 0, (t.2.2 : ℝ)]

theorem hnfMat_det (t : ℕ × ℕ × ℕ) : (hnfMat t).det = (t.1 : ℝ) * (t.2.2 : ℝ) := by
  simp [hnfMat, Matrix.det_fin_two]

/-- The action `z ↦ (a z + b)/d` of a Hermite triple on `ℍ`, through the matrix `[[a, b], [0, d]]`.
It is the Möbius action when `a d ≠ 0`; the fallback `z` is never used on `hnfData` triples. -/
def hnfAct (t : ℕ × ℕ × ℕ) (z : UpperHalfPlane) : UpperHalfPlane :=
  if h : (hnfMat t).det ≠ 0 then GeneralLinearGroup.mkOfDetNeZero (hnfMat t) h • z else z

/-- The classical weight `(a d)^{k-1} d^{-k}` of a Hermite triple. -/
def hnfWeight (k : ℤ) (t : ℕ × ℕ × ℕ) : ℂ :=
  ((t.1 * t.2.2 : ℕ) : ℂ) ^ (k - 1) * ((t.2.2 : ℕ) : ℂ) ^ (-k)

/-- The lattice operator `∑_{(a,b,d) ∈ hnfData n} (a d)^{k-1} d^{-k} F((a z + b)/d)`. -/
def latticeOp (k : ℤ) (n : ℕ) (F : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  ∑ t ∈ hnfData n, hnfWeight k t * F (hnfAct t z)

theorem hnfAct_eq_of_det {t : ℕ × ℕ × ℕ} (h : (hnfMat t).det ≠ 0) (z : UpperHalfPlane) :
    hnfAct t z = GeneralLinearGroup.mkOfDetNeZero (hnfMat t) h • z := by
  unfold hnfAct
  rw [dite_eq_left h]

/-- The dilate `z ↦ p z` is the Hermite triple `(p, 0, 1)`. -/
theorem hnfAct_dilate {p : ℕ} (hp : 0 < p) (z : UpperHalfPlane) :
    hnfAct (p, 0, 1) z = GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p hp) • z := by
  have h : (hnfMat (p, 0, 1)).det ≠ 0 := by
    rw [hnfMat_det]
    have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa using this
  rw [hnfAct_eq_of_det h]
  congr 1
  apply Units.ext
  rw [binaryHeckeDilate_real]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hnfMat, GeneralLinearGroup.mkOfDetNeZero]

/-- The translate `z ↦ (z + j)/p` is the Hermite triple `(1, j, p)`. -/
theorem hnfAct_translate {p : ℕ} (hp : 0 < p) (j : Fin p) (z : UpperHalfPlane) :
    hnfAct (1, j.val, p) z =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p hp j) • z := by
  have h : (hnfMat (1, j.val, p)).det ≠ 0 := by
    rw [hnfMat_det]
    have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    simpa using this
  rw [hnfAct_eq_of_det h]
  congr 1
  apply Units.ext
  rw [binaryHeckeTranslate_real]
  ext i j'
  fin_cases i <;> fin_cases j' <;> simp [hnfMat, GeneralLinearGroup.mkOfDetNeZero]

/-- For `p` prime, the Hermite triples of index `p` are the dilate and the `p` translates. -/
theorem hnfData_prime {p : ℕ} (hp : p.Prime) :
    hnfData (p ^ 1) = insert (p, 0, 1) (univ.image fun j : Fin p => ((1 : ℕ), j.val, p)) := by
  rw [pow_one]
  ext ⟨a, b, d⟩
  rw [mem_hnfData hp.pos, mem_insert, mem_image]
  constructor
  · rintro ⟨ha, had, hbd⟩
    have hdvd : a ∣ p := ⟨d, had.symm⟩
    rcases (Nat.dvd_prime hp).1 hdvd with ha1 | hap
    · subst ha1
      have hdp : d = p := by simpa using had
      subst hdp
      exact Or.inr ⟨⟨b, hbd⟩, mem_univ _, rfl⟩
    · subst hap
      have hd1 : d = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (had.trans (mul_one a).symm)
      subst hd1
      have hb0 : b = 0 := by
        have hbd' : b < 1 := hbd
        omega
      subst hb0
      exact Or.inl rfl
  · rintro (h | ⟨j, -, h⟩)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨hp.pos, by simp, by norm_num⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨one_pos, one_mul _, j.isLt⟩

theorem hnfWeight_dilate {p : ℕ} (k : ℤ) : hnfWeight k (p, 0, 1) = (p : ℂ) ^ (k - 1) := by
  simp [hnfWeight]

theorem hnfWeight_translate {p : ℕ} (hp : p.Prime) (k : ℤ) (j : ℕ) :
    hnfWeight k (1, j, p) = (p : ℂ)⁻¹ := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  unfold hnfWeight
  simp only [one_mul]
  rw [← zpow_add₀ hp0, show k - 1 + -k = -1 by ring, _root_.zpow_neg_one]

/-- Level one: the lattice operator at a prime `p` is the prime Hecke sum of
`HasPrimeHeckeRelations`, with dilate weight `p^{k-1}` and translate weight `p^{-1}`. -/
theorem latticeOp_one {p : ℕ} (hp : p.Prime) (k : ℤ) (F : UpperHalfPlane → ℂ)
    (z : UpperHalfPlane) :
    latticeOp k (p ^ 1) F z =
      (p : ℂ) ^ (k - 1) * F (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeDilate p hp.pos) • z) +
        (p : ℂ)⁻¹ * ∑ j : Fin p,
          F (GeneralLinearGroup.map (algebraMap ℚ ℝ) (binaryHeckeTranslate p hp.pos j) • z) := by
  unfold latticeOp
  rw [hnfData_prime hp, sum_insert, sum_image, mul_sum]
  · congr 1
    · rw [hnfWeight_dilate, hnfAct_dilate hp.pos z]
    · apply sum_congr rfl
      intro j _
      rw [hnfWeight_translate hp k j.val, hnfAct_translate hp.pos j z]
  · intro x _ y _ hxy
    exact Fin.ext (by simpa using congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hxy)
  · rw [mem_image]
    rintro ⟨j, -, h⟩
    simp only [Prod.mk.injEq] at h
    exact hp.one_lt.ne h.1

/-- The prime Hecke relation `λ(p) h = T_p h` of `HasPrimeHeckeRelations` is the statement
`λ(p) h(z) = latticeOp k p h z` for every prime `p` (with `p^1 = p`). -/
theorem hasPrimeHeckeRelations_iff_latticeOp (k : ℤ) (h : UpperHalfPlane → ℂ)
    (eigenvalues : Nat.Primes → ℂ) :
    HasPrimeHeckeRelations k h eigenvalues ↔
      ∀ (prime : Nat.Primes) (z : UpperHalfPlane),
        eigenvalues prime * h z = latticeOp k (prime.val ^ 1) h z := by
  constructor
  · intro relations prime z
    rw [latticeOp_one prime.property k h z]
    exact relations prime z
  · intro relations prime z
    rw [relations prime z, latticeOp_one prime.property k h z]

end TernaryPeriodPolynomials.Argument.LatticeCounts.LatticeOperator
