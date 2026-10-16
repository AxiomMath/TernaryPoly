module

public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.LevelOneEigenform
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.PairCharacterBound
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Eigen.Satake.CuspEisensteinSeparation

@[expose] public section


/-!
# Level-one cusp eigenforms from the pair character

For an inducing datum `D` with trivial character and nonzero associate pair, `n` odd and `n ≥ 3`,
a nonzero local joint generalized eigenspace of the pair character at the identity-plane (resp.
good-line) cusp produces a nonzero level-one cusp form `f` of weight `n + 3` with
`T_p f = (p + 1) p^{(n+1)/2} ω(diag(p, 1)) f` for every prime `p ≠ 3`, where `ω` is the Satake
scalar of the cuspidal datum.
-/

noncomputable section

open scoped ModularForm MatrixGroups
open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.RepresentationTheory
open TernaryPeriodPolynomials.HeckeEigen
open TernaryPeriodPolynomials.HeckeEigen.Satake
open TernaryPeriodPolynomials.SphericalDetection
open TernaryPeriodPolynomials.Spectral
open TernaryPeriodPolynomials.Spectral.LevelOneHecke
open TernaryPeriodPolynomials.Spectral.LocalUniqueness (two two_ne_three)

namespace TernaryPeriodPolynomials.MultiplicityOne

/-! ### Arithmetic of the eigenvalue -/

/-- `exp (-(k log p)) = (p^k)⁻¹`. -/
theorem exp_neg_mul_log (k p : ℕ) (hp : 0 < p) :
    Complex.exp (-((k : ℂ) * (Real.log p : ℂ))) = ((p : ℂ) ^ k)⁻¹ := by
  have h : -((k : ℂ) * (Real.log p : ℂ)) = ((-((k : ℝ) * Real.log p) : ℝ) : ℂ) := by
    rw [Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_natCast]
  rw [h, ← Complex.ofReal_exp, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (show (0 : ℝ) < (p : ℝ) by exact_mod_cast hp)]
  simp

theorem lam_alg (A p ω : ℂ) (hA : A ≠ 0) (hp : p ≠ 0) :
    A * A * ((p ^ 2 + p) * ((A * p)⁻¹ * ω)) = (p + 1) * A * ω := by
  rw [mul_inv]
  calc A * A * ((p ^ 2 + p) * ((A⁻¹ * p⁻¹) * ω))
      = (A * A⁻¹) * (p * p⁻¹) * ((p + 1) * A * ω) := by ring
    _ = (p + 1) * A * ω := by
      rw [mul_inv_cancel₀ hA, mul_inv_cancel₀ hp, one_mul, one_mul]

/-- For `n = 2m + 1`: `p^{n+1} (p² + p) p^{-(m+2)} ω = (p + 1) p^{m+1} ω`. -/
theorem lam_closed (n m : ℕ) (hm : n = 2 * m + 1) (p ω : ℂ) (hp : p ≠ 0) :
    p ^ (n + 1) * ((p ^ 2 + p) * ((p ^ (m + 2))⁻¹ * ω)) = (p + 1) * p ^ ((n + 1) / 2) * ω := by
  subst hm
  have h : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [h]
  have hA : p ^ (m + 1) ≠ 0 := pow_ne_zero _ hp
  have h1 : p ^ (2 * m + 1 + 1) = p ^ (m + 1) * p ^ (m + 1) := by ring
  have h2 : p ^ (m + 2) = p ^ (m + 1) * p := by ring
  rw [h1, h2]
  exact lam_alg _ p ω hA hp

/-! ### The pair character -/

variable {n : ℕ}

/-- For `n ≥ 3` the pair character at `T_2` is within `3/4` of `1`. -/
theorem pairChar_two_bound (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) (hn : 3 ≤ n)
    (hne : associatePair D ≠ ⊥) :
    ‖pairCharacter D hecke hhecke (TpExistence.tp two) - 1‖ ≤ 3 / 4 := by
  have h := PairCharacterBound.pairCharacter_tp_sub_one_norm_le D hχ hecke hhecke hne two
    two_ne_three
  refine h.trans ?_
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexp : Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((two.val : ℕ) : ℝ))) ≤ 1 / 8 := by
    have h8 : Real.exp (-(3 * Real.log 2)) = 1 / 8 := by
      rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
      norm_num
    rw [← h8]
    apply Real.exp_le_exp.mpr
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    change -(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ)) ≤ -(3 * Real.log 2)
    push_cast
    nlinarith
  change ((((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ)) *
      Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((2 : ℕ) : ℝ))) ≤ 3 / 4
  have : (((2 : ℕ) : ℝ)) ^ 2 + ((2 : ℕ) : ℝ) = 6 := by norm_num
  rw [this]
  change (6 : ℝ) * Real.exp (-(((n : ℝ) + 3) / 2 * Real.log ((two.val : ℕ) : ℝ))) ≤ 3 / 4
  linarith

/-- The `T_p` eigenvalue on the level-one cusp eigenform attached to a cuspidal datum `σ` at the
cohomological point: `(p + 1) p^{(n+1)/2} ω_σ(diag(p, 1))`. -/
def levelOneEigenvalue (n : ℕ) (σ : CuspidalRepresentation) (p : Nat.Primes) : ℂ :=
  ((p.val : ℂ) + 1) * (p.val : ℂ) ^ ((n + 1) / 2) * omega σ (Bo (dP p.property))

/-- **The closed form of the eigenvalue**: for the trivial character and `n` odd,
`p^{n+1} (c(T_p) - 1) = levelOneEigenvalue n D.cusp p` for the pair character `c`. -/
theorem pair_scalar_closed_form (D : InducingData n) (hχ : D.chi = trivialCharacter)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (hne : associatePair D ≠ ⊥) (hodd : Odd n) (p : Nat.Primes) (hp3 : p.val ≠ 3) :
    (p.val : ℂ) ^ (n + 1) * (pairCharacter D hecke hhecke (TpExistence.tp p) - 1) =
      levelOneEigenvalue n D.cusp p := by
  unfold levelOneEigenvalue
  obtain ⟨m, hm⟩ := hodd
  have hone : D.chi.toMonoidHom (sAd (pUnit p.property)) = 1 := by
    rw [hχ]
    rfl
  have hp : (p.val : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hE : Complex.exp (-(((n : ℂ) + 3) / 2 * (Real.log (p.val : ℝ) : ℂ))) =
      ((p.val : ℂ) ^ (m + 2))⁻¹ := by
    have h1 : -(((n : ℂ) + 3) / 2 * (Real.log (p.val : ℝ) : ℂ)) =
        -(((m + 2 : ℕ) : ℂ) * (Real.log (p.val : ℝ) : ℂ)) := by
      rw [hm]
      push_cast
      ring
    rw [h1]
    exact exp_neg_mul_log (m + 2) p.val p.property.pos
  rw [PairCharacterBound.pairCharacter_tp_eq D hecke hhecke hne p hp3, cuspPlaneEigenvalue, hone,
    add_sub_cancel_left, hE]
  exact lam_closed n m hm _ _ hp

/-! ### The eigenforms -/

/-- The identity-plane eigenform statement for any character equal to the trivial one. -/
theorem exists_eigenform_identityPlane_of_chi {χ : RankOneCharacter} {k : ℤ}
    (hχ : χ = trivialCharacter) (hk : k = (n : ℤ) + 3) (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hne : CuspReduction.localJoint n χ c .plane false ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree k
        (fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1)) := by
  subst hχ
  exact exists_levelOne_eigenform_identityPlane hk hn hodd c hc hne

/-- The good-line eigenform statement for any character equal to the trivial one. -/
theorem exists_eigenform_goodLine_of_chi {χ : RankOneCharacter} {k : ℤ}
    (hχ : χ = trivialCharacter) (hk : k = (n : ℤ) + 3) (hn : 0 < n) (hodd : Odd n)
    (c : HeckeCorrespondence → ℂ)
    (hc : ‖c (TpExistence.tp two) - 1‖ ≤ 3 / 4)
    (hne : CuspReduction.localJoint n χ c .line true ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      f ∈ LevelOneMultiplicityOne.eigenspaceAwayThree k
        (fun p => (p.val : ℂ) ^ (n + 1) * (c (TpExistence.tp p) - 1)) := by
  subst hχ
  exact exists_levelOne_eigenform_goodLine hk hn hodd c hc hne

/-- **The identity-plane cusp eigenform of a pair.** For `D` with trivial character, nonzero
associate pair, `n` odd and `n ≥ 3`, a nonzero local joint generalized eigenspace of the pair
character at the identity plane gives a nonzero level-one cusp form `f` of weight `n + 3` with
`T_p f = (p + 1) p^{(n+1)/2} ω(diag(p, 1)) f` for all primes `p ≠ 3`. -/
theorem exists_levelOne_eigenform_pair_identityPlane {k : ℤ} (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hk : k = (n : ℤ) + 3) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hodd : Odd n) (hn : 3 ≤ n)
    (hne : associatePair D ≠ ⊥)
    (hloc : CuspReduction.localJoint n D.chi (pairCharacter D hecke hhecke) .plane false ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      ∀ p : Nat.Primes, p.val ≠ 3 → levelOneHecke k p f = levelOneEigenvalue n D.cusp p • f := by
  have hc := pairChar_two_bound D hχ hecke hhecke hn hne
  obtain ⟨f, hf0, hf⟩ := exists_eigenform_identityPlane_of_chi hχ hk (by omega) hodd
    (pairCharacter D hecke hhecke) hc hloc
  refine ⟨f, hf0, fun p hp3 => ?_⟩
  rw [LevelOneMultiplicityOne.mem_eigenspaceAwayThree.mp hf p hp3]
  exact congrArg (fun a : ℂ => a • f) (pair_scalar_closed_form D hχ hecke hhecke hne hodd p hp3)

/-- **The good-line cusp eigenform of a pair**: same eigenvalues as at the identity plane. -/
theorem exists_levelOne_eigenform_pair_goodLine {k : ℤ} (D : InducingData n)
    (hχ : D.chi = trivialCharacter) (hk : k = (n : ℤ) + 3) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (hodd : Odd n) (hn : 3 ≤ n)
    (hne : associatePair D ≠ ⊥)
    (hloc : CuspReduction.localJoint n D.chi (pairCharacter D hecke hhecke) .line true ≠ ⊥) :
    ∃ f : CuspForm levelOne k, f ≠ 0 ∧
      ∀ p : Nat.Primes, p.val ≠ 3 → levelOneHecke k p f = levelOneEigenvalue n D.cusp p • f := by
  have hc := pairChar_two_bound D hχ hecke hhecke hn hne
  obtain ⟨f, hf0, hf⟩ := exists_eigenform_goodLine_of_chi hχ hk (by omega) hodd
    (pairCharacter D hecke hhecke) hc hloc
  refine ⟨f, hf0, fun p hp3 => ?_⟩
  rw [LevelOneMultiplicityOne.mem_eigenspaceAwayThree.mp hf p hp3]
  exact congrArg (fun a : ℂ => a • f) (pair_scalar_closed_form D hχ hecke hhecke hne hodd p hp3)

end TernaryPeriodPolynomials.MultiplicityOne
