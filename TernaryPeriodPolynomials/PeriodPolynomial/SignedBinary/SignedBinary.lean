module

public import TernaryPeriodPolynomials.Polynomial.Classification
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section


/-!
# The signed binary relation sets `𝓑_d^ε` of equation `eq:signed-binary` and the period spaces (MR-4)

Formalized by Claude Sonnet 5.5.

`SignedBinaryRelations ε q` is the literal
system `q(Y,X) = ε q(X,Y)`, `q(-X,Y) = q(X,-Y) = -ε q(X,Y)`, `q(X,0) = q(0,Y) = 0`, `N₂ q = 0` with
`N₂ q = q(X,Y) + q(-Y,X-Y) + q(Y-X,-X)`, and `signedBinary ε d` is the space of homogeneous polynomials of degree `d` satisfying it.

* `signedBinary_one_eq`: `𝓑_d = 𝓑_d^+ = 𝒫_d^{0,odd}(ℚ)` (`TernaryPoly.Paper.oddPeriodSpace ℚ d`);
* `signedBinary_neg_one_eq`: `𝓑_d^0 = 𝓑_d^- = 𝒫_d^{0,ev}(ℚ)` (`TernaryPoly.Paper.evenPeriodSpace ℚ d`).

Both are equalities of submodules of `MvPolynomial (Fin 2) ℚ`.  The paper's convention `𝓑_d^ε = 0` for `d < 0` is covered by indexing `d` by `ℕ`.
-/

open MvPolynomial

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

open TernaryPoly.Paper

/-- **The relations of equation `eq:signed-binary`** for the sign `ε`. -/
def SignedBinaryRelations (ε : ℚ) (q : Binary ℚ) : Prop :=
  bind₁ ![X 1, X 0] q = ε • q ∧ bind₁ ![-X 0, X 1] q = (-ε) • q ∧ bind₁ ![X 0, -X 1] q = (-ε) • q ∧
    bind₁ (![0, X 1] : Fin 2 → Binary ℚ) q = 0 ∧ bind₁ (![X 0, 0] : Fin 2 → Binary ℚ) q = 0 ∧
    q + bind₁ ![-X 1, X 0 - X 1] q + bind₁ ![X 1 - X 0, -X 0] q = 0

/-- **The space `𝓑_d^ε`**: homogeneous binary polynomials of degree `d` satisfying `eq:signed-binary`. -/
def signedBinary (ε : ℚ) (d : ℕ) : Submodule ℚ (Binary ℚ) where
  carrier := {q | q ∈ homogeneousSubmodule (Fin 2) ℚ d ∧ SignedBinaryRelations ε q}
  zero_mem' := ⟨zero_mem _, by simp [SignedBinaryRelations]⟩
  add_mem' := by
    rintro p q ⟨hp, hp₁, hp₂, hp₃, hp₄, hp₅, hp₆⟩ ⟨hq, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆⟩
    refine ⟨add_mem hp hq, by rw [map_add, hp₁, hq₁, smul_add], by rw [map_add, hp₂, hq₂, smul_add],
      by rw [map_add, hp₃, hq₃, smul_add], by rw [map_add, hp₄, hq₄, add_zero],
      by rw [map_add, hp₅, hq₅, add_zero], ?_⟩
    simp only [map_add]
    linear_combination hp₆ + hq₆
  smul_mem' := by
    rintro a q ⟨hq, hq₁, hq₂, hq₃, hq₄, hq₅, hq₆⟩
    refine ⟨Submodule.smul_mem _ a hq, by rw [map_smul, hq₁, smul_comm], by rw [map_smul, hq₂, smul_comm],
      by rw [map_smul, hq₃, smul_comm], by rw [map_smul, hq₄, smul_zero],
      by rw [map_smul, hq₅, smul_zero], ?_⟩
    simp only [map_smul]
    rw [← smul_add, ← smul_add, hq₆, smul_zero]

theorem mem_signedBinary {ε : ℚ} {d : ℕ} {q : Binary ℚ} :
    q ∈ signedBinary ε d ↔ q.IsHomogeneous d ∧ SignedBinaryRelations ε q := Iff.rfl

section Characterisation

variable {ε : ℚ} (hε : ε * ε = 1)

include hε

/-- For `ε² = 1`, the signed relations are the normalized period relations together with the parity `q(-X,Y) = -ε q`. -/
theorem signedRelations_iff {q : Binary ℚ} :
    SignedBinaryRelations ε q ↔ PeriodRelations q ∧ bind₁ ![-X 0, X 1] q = (-ε) • q := by
  have key : bind₁ ![-X 0, X 1] q = (-ε) • q →
      binaryEval q (-X 1 : Binary ℚ) (X 0) = (-ε) • binaryEval q (X 1 : Binary ℚ) (X 0) := by
    intro ho
    have h := congrArg (fun p => binaryEval p (X 1 : Binary ℚ) (X 0)) ho
    simp only [binaryEval, bind₁_bind₁, bind_vec2, map_smul] at h
    simpa [binaryEval] using h
  constructor
  · rintro ⟨hs, ho, -, ha, hb, hn⟩
    refine ⟨⟨ha, hb, ?_, hn⟩, ho⟩
    have h' := key ho
    have hs' : binaryEval q (X 1 : Binary ℚ) (X 0) = ε • q := hs
    change q + binaryEval q (-X 1 : Binary ℚ) (X 0) = 0
    rw [h', hs', smul_smul, neg_mul, hε, neg_smul, one_smul, add_neg_cancel]
  · rintro ⟨hq, ho⟩
    have two := hq.identities.eval_two_term (X 0 : Binary ℚ) (X 1)
    rw [binaryEval_X] at two
    have h' := key ho
    have hs : binaryEval q (X 1 : Binary ℚ) (X 0) = ε • q := by
      have e : q = ε • binaryEval q (X 1 : Binary ℚ) (X 0) := by
        have e2 : binaryEval q (-X 1 : Binary ℚ) (X 0) = -q := eq_neg_of_add_eq_zero_right two
        rw [h', neg_smul] at e2
        exact (neg_inj.mp e2).symm
      calc binaryEval q (X 1 : Binary ℚ) (X 0) = (ε * ε) • binaryEval q (X 1 : Binary ℚ) (X 0) := by
            rw [hε, one_smul]
        _ = ε • q := by rw [mul_smul, ← e]
    refine ⟨hs, ho, ?_, hq.axis_first, hq.axis_second, hq.three_term⟩
    have h2 := congrArg (fun p => binaryEval p (X 0 : Binary ℚ) (-X 1)) hs
    simp only [binaryEval, bind₁_bind₁, bind_vec2, map_smul] at h2
    have h2' : binaryEval q (-X 1 : Binary ℚ) (X 0) = ε • binaryEval q (X 0 : Binary ℚ) (-X 1) := by
      simpa [binaryEval] using h2
    have hm : binaryEval q (-X 1 : Binary ℚ) (X 0) = -q := eq_neg_of_add_eq_zero_right two
    have : binaryEval q (X 0 : Binary ℚ) (-X 1) = (-ε) • q := by
      calc binaryEval q (X 0 : Binary ℚ) (-X 1) = (ε * ε) • binaryEval q (X 0 : Binary ℚ) (-X 1) := by
            rw [hε, one_smul]
        _ = ε • (-q) := by rw [mul_smul, ← h2', hm]
        _ = (-ε) • q := by rw [smul_neg, neg_smul]
    exact this

end Characterisation

/-- **MR-4, symmetric case**: `𝓑_d = 𝓑_d^+ = 𝒫_d^{0,odd}(ℚ)` (equality of submodules of `ℚ[X,Y]`). -/
theorem signedBinary_one_eq (d : ℕ) : signedBinary 1 d = oddPeriodSpace ℚ d := by
  ext q
  rw [mem_signedBinary, signedRelations_iff (by norm_num : (1 : ℚ) * 1 = 1)]
  simp only [oddPeriodSpace, Submodule.mem_inf, mem_periodSpace, LinearMap.mem_ker, LinearMap.add_apply,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, neg_smul, one_smul, add_eq_zero_iff_eq_neg]
  tauto

/-- **MR-4, alternating case**: `𝓑_d^0 = 𝓑_d^- = 𝒫_d^{0,ev}(ℚ)` (equality of submodules of `ℚ[X,Y]`). -/
theorem signedBinary_neg_one_eq (d : ℕ) : signedBinary (-1) d = evenPeriodSpace ℚ d := by
  ext q
  rw [mem_signedBinary, signedRelations_iff (by norm_num : (-1 : ℚ) * -1 = 1)]
  simp only [evenPeriodSpace, Submodule.mem_inf, mem_periodSpace, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, LinearMap.id_apply, neg_neg, one_smul, sub_eq_zero]
  tauto

/-- The same two statements as linear equivalences compatible with the inclusions into `ℚ[X,Y]`. -/
def signedBinaryOddEquiv (d : ℕ) : signedBinary 1 d ≃ₗ[ℚ] oddPeriodSpace ℚ d :=
  LinearEquiv.ofEq _ _ (signedBinary_one_eq d)

/-- `𝓑_d^0 ≃ 𝒫_d^{0,ev}(ℚ)`, the identity on underlying polynomials. -/
def signedBinaryEvenEquiv (d : ℕ) : signedBinary (-1) d ≃ₗ[ℚ] evenPeriodSpace ℚ d :=
  LinearEquiv.ofEq _ _ (signedBinary_neg_one_eq d)

@[simp] theorem signedBinaryOddEquiv_apply (d : ℕ) (q : signedBinary 1 d) :
    ((signedBinaryOddEquiv d q : oddPeriodSpace ℚ d) : Binary ℚ) = q := rfl

@[simp] theorem signedBinaryEvenEquiv_apply (d : ℕ) (q : signedBinary (-1) d) :
    ((signedBinaryEvenEquiv d q : evenPeriodSpace ℚ d) : Binary ℚ) = q := rfl

end TernaryPeriodPolynomials.Argument.Identities
