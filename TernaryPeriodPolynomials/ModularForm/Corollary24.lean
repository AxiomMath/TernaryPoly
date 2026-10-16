module

public import TernaryPeriodPolynomials.ModularForm.PeriodTowers
public import TernaryPeriodPolynomials.Polynomial.NormKernelDegree

@[expose] public section


/-!
# Corollary 2.4 (`cor:period-towers`) as one theorem

Formalized by Claude Sonnet 5.5.

> **Corollary 2.4.** If a symmetric solution `f ∈ V_n` satisfies `J_f = 0`, then uniquely
> `f = ∑_{j ≥ 0} w^{e_j} Φ(q_j)`, with `e_j = 2j`, `q_j ∈ 𝓑_{n-2j}` for `n` even and
> `e_j = 2j - 1`, `q_j ∈ 𝓑_{n+1-2j}` for `n` odd. The sum is finite. In odd degree, its first
> term is interpreted as the polynomial lift `L(q_0)`.

Conventions. `w = x + y + z`; `𝓑_d` is `SymmetricBinaryPeriodRelations ∧ IsHomogeneous d`;
`J_f` is `TernaryPoly.symmetricTodd f` (`PolynomialBridge.map_symmetricTodd` identifies it with the
Bernoulli obstruction of `eq:Jdef`); a "symmetric solution" is `PeriodRelations f ∧ S f = f`;
"finite sum" is a family indexed by `Fin k`; "uniquely" means that two such families agree after
extension by zero (`PeriodTowers.extendZero`). In odd degree the polynomial lift `L(q_j)` is a
polynomial `l_j` with `Φ(q_j) = w l_j`, and the term `w^{2j-1} Φ(q_j)` is `w^{2j} l_j`; the
statement records both `f = ∑ w^{2j} l_j` and `w f = ∑ w^{2j} Φ(q_j)`.
-/

open MvPolynomial TernaryPoly

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Statements.Corollary24

open PeriodTowers

local notation "W" => (X 0 + X 1 + X 2 : TernaryPolynomial)
local notation "BP" => MvPolynomial (Fin 2) ℚ

/-- A finite even-degree tower `f = ∑_j w^{2j} Φ(q_j)`, `q_j ∈ 𝓑_{n-2j}`. -/
def EvenTower (n : ℕ) (f : TernaryPolynomial) (k : ℕ) (q : Fin k → BP) : Prop :=
  (∀ i, SymmetricBinaryPeriodRelations (q i) ∧ (q i).IsHomogeneous (n - 2 * (i : ℕ))) ∧
    f = ∑ i : Fin k, W ^ (2 * (i : ℕ)) * binaryPeriodLift (q i)

/-- A finite odd-degree tower `f = ∑_j w^{2j-1} Φ(q_j)`, `q_j ∈ 𝓑_{n+1-2j}`, first term `L(q_0)`. -/
def OddTower (n : ℕ) (f : TernaryPolynomial) (k : ℕ) (q : Fin k → BP)
    (l : Fin k → TernaryPolynomial) : Prop :=
  (∀ i, SymmetricBinaryPeriodRelations (q i) ∧ (q i).IsHomogeneous (n + 1 - 2 * (i : ℕ)) ∧
      binaryPeriodLift (q i) = W * l i) ∧
    f = ∑ i : Fin k, W ^ (2 * (i : ℕ)) * l i ∧
    W * f = ∑ i : Fin k, W ^ (2 * (i : ℕ)) * binaryPeriodLift (q i)

/-- **Corollary 2.4** (`cor:period-towers`, `eq:sym-tower`), existence and uniqueness, both
parities, `n = 0` included. -/
theorem corollary_2_4 {n : ℕ} {f : TernaryPolynomial} (hf : f.IsHomogeneous n)
    (hrel : PeriodRelations f) (hs : S f = f) (hJ : symmetricTodd f = 0) :
    (Even n → ∃ (k : ℕ) (q : Fin k → BP), EvenTower n f k q ∧
      ∀ (k' : ℕ) (q' : Fin k' → BP), EvenTower n f k' q' →
        ∀ j : ℕ, extendZero q j = extendZero q' j) ∧
    (Odd n → ∃ (k : ℕ) (q : Fin k → BP) (l : Fin k → TernaryPolynomial), OddTower n f k q l ∧
      ∀ (k' : ℕ) (q' : Fin k' → BP) (l' : Fin k' → TernaryPolynomial), OddTower n f k' q' l' →
        ∀ j : ℕ, extendZero q j = extendZero q' j ∧ extendZero l j = extendZero l' j) := by
  refine ⟨fun he => ?_, fun ho => ?_⟩
  · have hex : ∃ (k : ℕ) (q : Fin k → BP), EvenTower n f k q := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · have h0 : f = 0 :=
          (TernaryPeriodPolynomials.solution_homogeneous_symmetric_alternating_parts (F := ℚ)).2.2 0 f (by norm_num) hf hrel
        exact ⟨0, fun i => i.elim0, fun i => i.elim0, by simp [h0]⟩
      · obtain ⟨k, q, hq, hfq⟩ := symmetric_even_period_tower hn he hf hrel hs hJ
        exact ⟨k, q, hq, hfq⟩
    obtain ⟨k, q, hT⟩ := hex
    refine ⟨k, q, hT, fun k' q' hT' j => ?_⟩
    exact symmetric_even_period_tower_unique q q' (fun i => (hT.1 i).1) (fun i => (hT'.1 i).1)
      (hT.2.symm.trans hT'.2) j
  · obtain ⟨k, q, l, hql, hfl⟩ := symmetric_odd_period_tower hf ho hrel.1 hs hJ
    have hT : OddTower n f k q l := by
      refine ⟨hql, hfl, ?_⟩
      rw [hfl, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [(hql i).2.2]
      ring
    refine ⟨k, q, l, hT, fun k' q' l' hT' j => ?_⟩
    exact symmetric_period_tower_unique q l q' l'
      (fun i => ⟨(hT.1 i).1, (hT.1 i).2.2⟩) (fun i => ⟨(hT'.1 i).1, (hT'.1 i).2.2⟩)
      (hT.2.1.symm.trans hT'.2.1) j

end TernaryPeriodPolynomials.Argument.Statements.Corollary24
