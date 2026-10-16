module

public import TernaryPeriodPolynomials.ArithmeticCohomology.ApartmentPairing.Orient.CellsAbove

@[expose] public section


/-!
# Rational data of the flags of the standard top cell (finite checks)

The flag simplices of the cone chain of the standard top cell `T₀` are `(b(T₀), b(F₂), b(F₁), b(F₀))`
with `F₂ = T₀ ∪ {i}`, `F₁ = T₀ ∪ {i,j}`, `F₀ = Mk k` a vertex.  Their linearized vertices are the
rational vectors `vq k i j`.  Finite checks:

* `outside_all`: for every flag other than `f0 = (k,i,j) = (0,9,11)` the point `Pq = (1/30,-1/120,1/20)`
  lies outside the simplex (Cramer's rule, `outsideQ`);
* `tri_all`: the plane of every outer triangle `(b(F₂),b(F₁),b(F₀))` stays at `ℓ¹`-distance `≥ 1/3`
  from the origin (`triOK`);
* `Pq_sum`, `f0_det`, `Pq_norm`: `Pq` is `(1/30)(w₁+w₂+w₃)` for the flag `f0`, which is positively
  oriented, and `|Pq|² < 1/9`;
* `bLq_X2_inj`, `bLq_X1_inj`, `bLq_Mk_inj`: the barycentres separate the faces of `f0`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
open scoped Classical
open TernaryPeriodPolynomials.Argument.Lemma33.Retract
  TernaryPeriodPolynomials.Argument.Lemma33.Retract.Cell0Geometry
  TernaryPeriodPolynomials.FreeResolution

namespace TernaryPeriodPolynomials.Argument.Lemma33.Orient

/-! ### Rational test data for the flags of the standard top cell -/

/-- Determinant of three rational vectors. -/
def det3q (u v w : Fin 3 → ℚ) : ℚ :=
  u 0 * (v 1 * w 2 - v 2 * w 1) - u 1 * (v 0 * w 2 - v 2 * w 0) + u 2 * (v 0 * w 1 - v 1 * w 0)

/-- The point `p` lies outside the simplex with vertices `0, w1, w2, w3` (Cramer's rule). -/
def outsideQ (w1 w2 w3 p : Fin 3 → ℚ) : Prop :=
  (0 < det3q w1 w2 w3 ∧ (det3q p w2 w3 < 0 ∨ det3q w1 p w3 < 0 ∨ det3q w1 w2 p < 0 ∨
      det3q w1 w2 w3 < det3q p w2 w3 + det3q w1 p w3 + det3q w1 w2 p)) ∨
  (det3q w1 w2 w3 < 0 ∧ (0 < det3q p w2 w3 ∨ 0 < det3q w1 p w3 ∨ 0 < det3q w1 w2 p ∨
      det3q p w2 w3 + det3q w1 p w3 + det3q w1 w2 p < det3q w1 w2 w3))

instance (w1 w2 w3 p : Fin 3 → ℚ) : Decidable (outsideQ w1 w2 w3 p) := by
  unfold outsideQ; infer_instance

/-- Cross product. -/
def crossq (u v : Fin 3 → ℚ) : Fin 3 → ℚ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- `ℓ¹`-norm. -/
def l1q (n : Fin 3 → ℚ) : ℚ := |n 0| + |n 1| + |n 2|

/-- The plane through `v1, v2, v3` stays at `ℓ¹`-distance `≥ 1/3` from the origin. -/
def triOK (v1 v2 v3 : Fin 3 → ℚ) : Prop :=
  0 < l1q (crossq (v2 - v1) (v3 - v1)) ∧ l1q (crossq (v2 - v1) (v3 - v1)) ≤ 3 * |det3q v1 v2 v3|

instance (v1 v2 v3 : Fin 3 → ℚ) : Decidable (triOK v1 v2 v3) := by
  unfold triOK; infer_instance

/-- The index set of the facet `T₀ ∪ {i}`. -/
def X2 (i : Fin 13) : Finset (Fin 13) := insert i {0, 1, 2}

/-- The index set of the edge `T₀ ∪ {i, j}`. -/
def X1 (i j : Fin 13) : Finset (Fin 13) := insert j (X2 i)

/-- A flag of the standard top cell: vertex `k` and two distinct extra lines `i, j` of it. -/
def valid (k : Fin 16) (i j : Fin 13) : Prop :=
  i ∈ Mk k ∧ j ∈ Mk k ∧ 3 ≤ i.val ∧ 3 ≤ j.val ∧ i ≠ j

instance (k : Fin 16) (i j : Fin 13) : Decidable (valid k i j) := by
  unfold valid; infer_instance

/-- The linearized vertices `(0, b(facet), b(edge), b(vertex))` of the flag simplex. -/
def vq (k : Fin 16) (i j : Fin 13) : Fin 4 → Fin 3 → ℚ :=
  ![fun _ => 0, bLq (X2 i), bLq (X1 i j), bLq (Mk k)]

/-- The chosen flag. -/
def f0 : Fin 16 × Fin 13 × Fin 13 := (0, 9, 11)

/-- The chosen point near the identity. -/
def Pq : Fin 3 → ℚ := ![1 / 30, -1 / 120, 1 / 20]

theorem f0_valid : valid f0.1 f0.2.1 f0.2.2 := by decide

theorem outside_all : ∀ k : Fin 16, ∀ i j : Fin 13, valid k i j → (k, i, j) ≠ f0 →
    outsideQ (vq k i j 1) (vq k i j 2) (vq k i j 3) Pq := by
  decide +kernel

theorem tri_all : ∀ k : Fin 16, ∀ i j : Fin 13, valid k i j →
    triOK (vq k i j 1) (vq k i j 2) (vq k i j 3) := by
  decide +kernel


/-- Uniqueness of the facet with a given barycentre. -/
theorem bLq_X2_inj : ∀ i : Fin 13, 3 ≤ i.val → (∃ k, i ∈ Mk k) → bLq (X2 i) = bLq (X2 9) → i = 9 := by
  decide +kernel

/-- Uniqueness of the edge with a given barycentre, among the edges of the facet `X2 9`. -/
theorem bLq_X1_inj : ∀ j : Fin 13, 3 ≤ j.val → j ≠ 9 → (∃ k, 9 ∈ Mk k ∧ j ∈ Mk k) →
    bLq (X1 9 j) = bLq (X1 9 11) → j = 11 := by
  decide +kernel

/-- Uniqueness of the vertex with a given barycentre. -/
theorem bLq_Mk_inj : ∀ k : Fin 16, bLq (Mk k) = bLq (Mk 0) → k = 0 := by
  decide +kernel

theorem Pq_sum : ∀ c, Pq c = (1 / 30 : ℚ) * (vq f0.1 f0.2.1 f0.2.2 1 c + vq f0.1 f0.2.1 f0.2.2 2 c +
    vq f0.1 f0.2.1 f0.2.2 3 c) := by
  decide +kernel

theorem f0_det : 0 < det3q (vq f0.1 f0.2.1 f0.2.2 1) (vq f0.1 f0.2.1 f0.2.2 2)
    (vq f0.1 f0.2.1 f0.2.2 3) := by
  decide +kernel

theorem Pq_norm : Pq 0 ^ 2 + Pq 1 ^ 2 + Pq 2 ^ 2 < 1 / 9 := by
  decide +kernel

end TernaryPeriodPolynomials.Argument.Lemma33.Orient
