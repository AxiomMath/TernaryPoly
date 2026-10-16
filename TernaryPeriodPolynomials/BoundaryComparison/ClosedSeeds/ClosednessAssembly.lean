module

public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessHardTriples
public import TernaryPeriodPolynomials.BoundaryComparison.ClosedSeeds.ClosednessHardTriples2

@[expose] public section


/-! Clause (i) of Lemma C.3 (`ar:lem:seed`): final assembly. Combines the trivial cases
(repeated index, or an index equal to `4`, from `ClosednessTrivial.lean`) with the four
nontrivial representative triples (`Alt3_012`, `Alt3_013` from `ClosednessHardTriples.lean`;
`Alt3_023`, `Alt3_123` from `ClosednessHardTriples2.lean`), propagated to all `6` permutations of
each `3`-element subset of `{0,1,2,3}` via the antisymmetry lemmas `Alt3_swap_ij/jk/ik`, into the
single statement `∀ i j k, Alt3 n h m p i j k = 0` matching clause (i) of `seed_closed_equivariant` verbatim.
Feeds `TernaryPeriodPolynomials.seed_closed_equivariant`. -/


open MvPolynomial

namespace TernaryPeriodPolynomials.Argument

/-- From one vanishing ordering `Alt3 p a b c = 0`, every other ordering of the same three
indices also vanishes, via the three transposition lemmas. -/
theorem Alt3_perm_zero (n : ℕ) (h : ℂ → ℂ) (m : Fin 3 →₀ ℕ) (p : Fin 5 → ℝ) (a b c : Fin 5)
    (hbase : Alt3 n h m p a b c = 0) :
    Alt3 n h m p a c b = 0 ∧ Alt3 n h m p b a c = 0 ∧ Alt3 n h m p c b a = 0 ∧
      Alt3 n h m p b c a = 0 ∧ Alt3 n h m p c a b = 0 := by
  have hacb : Alt3 n h m p a c b = 0 := by rw [Alt3_swap_jk, hbase, neg_zero]
  have hbac : Alt3 n h m p b a c = 0 := by rw [Alt3_swap_ij, hbase, neg_zero]
  have hcba : Alt3 n h m p c b a = 0 := by rw [Alt3_swap_ik, hbase, neg_zero]
  have hbca : Alt3 n h m p b c a = 0 := by rw [Alt3_swap_ij, hcba, neg_zero]
  have hcab : Alt3 n h m p c a b = 0 := by rw [Alt3_swap_ij, hacb, neg_zero]
  exact ⟨hacb, hbac, hcba, hbca, hcab⟩

/-- Clause (i) of Lemma C.3: the seed `ω_h` is closed, coefficientwise, for every triple of
coordinate indices. Matches the first conjunct of `seed_closed_equivariant` verbatim (via `Alt3`'s definition). -/
theorem seed_closed (n : ℕ) (h : ℂ → ℂ) (p : Fin 5 → ℝ) (_hp3 : 0 < p 3)
    (hdiff : DifferentiableAt ℂ h (seedTau p)) (m : Fin 3 →₀ ℕ) (i j k : Fin 5) :
    coordPartial (fun q => (seedForm n h q j k).coeff m) i p -
      coordPartial (fun q => (seedForm n h q i k).coeff m) j p +
      coordPartial (fun q => (seedForm n h q i j).coeff m) k p = 0 := by
  show Alt3 n h m p i j k = 0
  by_cases hij : i = j
  · rw [hij]; exact Alt3_eq_ij n h m p j k
  by_cases hjk : j = k
  · rw [hjk]; exact Alt3_eq_jk n h m p i k
  by_cases hik : i = k
  · rw [hik]; exact Alt3_eq_ik n h m p k j
  by_cases hi4 : i = 4
  · rw [hi4]; exact Alt3_dim4_left n h m p j k
  by_cases hj4 : j = 4
  · rw [hj4]; exact Alt3_dim4_mid n h m p i k
  by_cases hk4 : k = 4
  · rw [hk4]; exact Alt3_dim4_right n h m p i j
  obtain ⟨h012_acb, h012_bac, h012_cba, h012_bca, h012_cab⟩ :=
    Alt3_perm_zero n h m p 0 1 2 (Alt3_012 n h m p)
  obtain ⟨h013_acb, h013_bac, h013_cba, h013_bca, h013_cab⟩ :=
    Alt3_perm_zero n h m p 0 1 3 (Alt3_013 n h m p)
  obtain ⟨h023_acb, h023_bac, h023_cba, h023_bca, h023_cab⟩ :=
    Alt3_perm_zero n h m p 0 2 3 (Alt3_023 n h m p hdiff)
  obtain ⟨h123_acb, h123_bac, h123_cba, h123_bca, h123_cab⟩ :=
    Alt3_perm_zero n h m p 1 2 3 (Alt3_123 n h m p hdiff)
  -- Deterministic dispatch (no backtracking search): fix `i`, then `j`, then `k` via explicit
  -- `by_cases` on each candidate literal value, deriving the one value `omega` leaves once three
  -- of `{0,1,2,3,4}` are excluded.
  by_cases hi0 : i = 0
  · subst hi0
    by_cases hj1 : j = 1
    · subst hj1
      by_cases hk2 : k = 2
      · subst hk2; exact Alt3_012 n h m p
      · have hk3 : k = 3 := by omega
        subst hk3; exact Alt3_013 n h m p
    by_cases hj2 : j = 2
    · subst hj2
      by_cases hk1 : k = 1
      · subst hk1; exact h012_acb
      · have hk3 : k = 3 := by omega
        subst hk3; exact Alt3_023 n h m p hdiff
    by_cases hj3 : j = 3
    · subst hj3
      by_cases hk1 : k = 1
      · subst hk1; exact h013_acb
      · have hk2 : k = 2 := by omega
        subst hk2; exact h023_acb
    exfalso; omega
  by_cases hi1 : i = 1
  · subst hi1
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hk2 : k = 2
      · subst hk2; exact h012_bac
      · have hk3 : k = 3 := by omega
        subst hk3; exact h013_bac
    by_cases hj2 : j = 2
    · subst hj2
      by_cases hk0 : k = 0
      · subst hk0; exact h012_bca
      · have hk3 : k = 3 := by omega
        subst hk3; exact Alt3_123 n h m p hdiff
    by_cases hj3 : j = 3
    · subst hj3
      by_cases hk0 : k = 0
      · subst hk0; exact h013_bca
      · have hk2 : k = 2 := by omega
        subst hk2; exact h123_acb
    exfalso; omega
  by_cases hi2 : i = 2
  · subst hi2
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hk1 : k = 1
      · subst hk1; exact h012_cab
      · have hk3 : k = 3 := by omega
        subst hk3; exact h023_bac
    by_cases hj1 : j = 1
    · subst hj1
      by_cases hk0 : k = 0
      · subst hk0; exact h012_cba
      · have hk3 : k = 3 := by omega
        subst hk3; exact h123_bac
    by_cases hj3 : j = 3
    · subst hj3
      by_cases hk0 : k = 0
      · subst hk0; exact h023_bca
      · have hk1 : k = 1 := by omega
        subst hk1; exact h123_bca
    exfalso; omega
  by_cases hi3 : i = 3
  · subst hi3
    by_cases hj0 : j = 0
    · subst hj0
      by_cases hk1 : k = 1
      · subst hk1; exact h013_cab
      · have hk2 : k = 2 := by omega
        subst hk2; exact h023_cab
    by_cases hj1 : j = 1
    · subst hj1
      by_cases hk0 : k = 0
      · subst hk0; exact h013_cba
      · have hk2 : k = 2 := by omega
        subst hk2; exact h123_cab
    by_cases hj2 : j = 2
    · subst hj2
      by_cases hk0 : k = 0
      · subst hk0; exact h023_cba
      · have hk1 : k = 1 := by omega
        subst hk1; exact h123_cba
    exfalso; omega
  exfalso; omega

end TernaryPeriodPolynomials.Argument
