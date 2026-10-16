module

public import TernaryPeriodPolynomials.Building.FreeResolution.Lines
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section


/-!
# The perfect ternary form `A₃`

Original work by Claude Opus 5.5.

The form `Q₀(x) = x₀² + x₁² + x₂² + x₀x₁ + x₀x₂ + x₁x₂`, with `2Q₀(x) = x₀² + x₁² + x₂² +
(x₀ + x₁ + x₂)²`, takes integer values, is at least `1` on nonzero integer vectors, and equals `1`
exactly on the six lines `M₀ = {e₀, e₁, e₂, e₀ − e₁, e₀ − e₂, e₁ − e₂}`. Their rank-one forms are a
basis of the ternary forms; `U₀ i` is the dual basis (`U₀ i [m k] = δᵢₖ`). The Voronoi neighbour of
`A₀` across the facet opposite `m i` is `A₀ + U₀ i`, again a `GL₃(ℤ)`-translate of `A₀`, whose new
minimal vector `mNew i` satisfies `R(mNew i) + R(m i) ∈ span {R(m k) | k ≠ i}` for the rank-one
coordinates `R`. All of this is explicit finite computation.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix

/-- The six minimal vectors of `A₀`. -/
def m : Fin 6 → Vec :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]

/-- The Gram matrix of the perfect form `A₃`. -/
def A0 : Form := !![1, 1 / 2, 1 / 2; 1 / 2, 1, 1 / 2; 1 / 2, 1 / 2, 1]

theorem A0_transpose : A0ᵀ = A0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The integer values of `A₀`. -/
def Q0 (x : Vec) : ℤ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 0 * x 1 + x 0 * x 2 + x 1 * x 2

theorem qf_A0 (x : Vec) : qf A0 x = (Q0 x : ℚ) := by
  simp [qf, A0, Q0, Fin.sum_univ_three]
  ring

theorem one_le_sq_of_ne_zero {a : ℤ} (h : a ≠ 0) : 1 ≤ a ^ 2 := by
  rcases lt_or_gt_of_ne h with h' | h' <;> nlinarith

theorem bounds_of_sq_le_two {a : ℤ} (h : a ^ 2 ≤ 2) : -1 ≤ a ∧ a ≤ 1 := by
  constructor <;> by_contra hc <;> push Not at hc <;> nlinarith

theorem two_Q0 (x : Vec) : 2 * Q0 x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + (x 0 + x 1 + x 2) ^ 2 := by
  unfold Q0
  ring

theorem Q0_pos {x : Vec} (hx : x ≠ 0) : 1 ≤ Q0 x := by
  have h2 := two_Q0 x
  have hne : x 0 ≠ 0 ∨ x 1 ≠ 0 ∨ x 2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2
  have hpos : 1 ≤ 2 * Q0 x := by
    rw [h2]
    rcases hne with h | h | h
    · have : 1 ≤ x 0 ^ 2 := one_le_sq_of_ne_zero h
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 0 + x 1 + x 2)]
    · have : 1 ≤ x 1 ^ 2 := one_le_sq_of_ne_zero h
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 0 + x 1 + x 2)]
    · have : 1 ≤ x 2 ^ 2 := one_le_sq_of_ne_zero h
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1 + x 2)]
  omega

theorem qf_A0_ge_one {x : Vec} (hx : x ≠ 0) : 1 ≤ qf A0 x := by
  rw [qf_A0]
  exact_mod_cast Q0_pos hx

theorem small_solutions :
    ∀ a ∈ ({-1, 0, 1} : Finset ℤ), ∀ b ∈ ({-1, 0, 1} : Finset ℤ), ∀ c ∈ ({-1, 0, 1} : Finset ℤ),
      Q0 ![a, b, c] = 1 → ∃ i : Fin 6, ![a, b, c] = m i ∨ ![a, b, c] = -m i := by
  decide

theorem Q0_m (i : Fin 6) : Q0 (m i) = 1 := by
  fin_cases i <;> decide

theorem qf_A0_eq_one_iff (x : Vec) : qf A0 x = 1 ↔ ∃ i : Fin 6, x = m i ∨ x = -m i := by
  rw [qf_A0]
  constructor
  · intro h
    have hQ : Q0 x = 1 := by exact_mod_cast h
    have h2 := two_Q0 x
    rw [hQ] at h2
    have b0 : -1 ≤ x 0 ∧ x 0 ≤ 1 := bounds_of_sq_le_two (by
      nlinarith [sq_nonneg (x 1), sq_nonneg (x 2), sq_nonneg (x 0 + x 1 + x 2)])
    have b1 : -1 ≤ x 1 ∧ x 1 ≤ 1 := bounds_of_sq_le_two (by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 2), sq_nonneg (x 0 + x 1 + x 2)])
    have b2 : -1 ≤ x 2 ∧ x 2 ≤ 1 := bounds_of_sq_le_two (by
      nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 0 + x 1 + x 2)])
    have hx : x = ![x 0, x 1, x 2] := by
      funext i
      fin_cases i <;> rfl
    have m0 : x 0 ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have m1 : x 1 ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    have m2 : x 2 ∈ ({-1, 0, 1} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hx] at hQ ⊢
    exact small_solutions _ m0 _ m1 _ m2 hQ
  · rintro ⟨i, rfl | rfl⟩
    · exact_mod_cast Q0_m i
    · have : Q0 (-m i) = Q0 (m i) := by
        simp only [Q0, Pi.neg_apply]
        ring
      rw [this]
      exact_mod_cast Q0_m i

/-! ### The dual basis -/

/-- The dual basis of the rank-one forms of the minimal vectors: `U₀ i [m k] = δᵢₖ`. -/
def U0 : Fin 6 → Form :=
  ![!![1, 1 / 2, 1 / 2; 1 / 2, 0, 0; 1 / 2, 0, 0],
    !![0, 1 / 2, 0; 1 / 2, 1, 1 / 2; 0, 1 / 2, 0],
    !![0, 0, 1 / 2; 0, 0, 1 / 2; 1 / 2, 1 / 2, 1],
    !![0, -1 / 2, 0; -1 / 2, 0, 0; 0, 0, 0],
    !![0, 0, -1 / 2; 0, 0, 0; -1 / 2, 0, 0],
    !![0, 0, 0; 0, 0, -1 / 2; 0, -1 / 2, 0]]

theorem U0_transpose (i : Fin 6) : (U0 i)ᵀ = U0 i := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;> rfl

theorem qf_U0 (i k : Fin 6) : qf (U0 i) (m k) = if i = k then 1 else 0 := by
  fin_cases i <;> fin_cases k <;>
    norm_num [qf, U0, m, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- Every symmetric form is the combination of the dual basis with its values at the minimal
vectors. -/
theorem expand0 (X : Form) (hX : Xᵀ = X) : X = ∑ i, qf X (m i) • U0 i := by
  have hs : ∀ a b, X b a = X a b := fun a b => by
    rw [← Matrix.transpose_apply X a b, hX]
  have h10 := hs 1 0
  have h20 := hs 2 0
  have h21 := hs 2 1
  ext a b
  have ha : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> decide
  have hb : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> decide
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    norm_num [qf, U0, m, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail] <;> linarith

/-! ### The neighbours -/

/-- Integral matrices with `A₀ + U₀ i = gᵢᵀ A₀ gᵢ`. -/
def gMat : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![-1, -1, -1; -1, 0, 0; 1, 0, 1],
    !![-1, -1, -1; 0, -1, 0; 0, 1, 1],
    !![-1, -1, -1; 0, 0, -1; 0, 1, 1],
    !![-1, 0, -1; 0, -1, 0; 0, 1, 1],
    !![-1, -1, 0; 0, 0, -1; 0, 1, 1],
    !![-1, -1, 0; 0, 0, -1; 0, 1, 0]]

/-- Their inverses. -/
def gInv : Fin 6 → Matrix (Fin 3) (Fin 3) ℤ :=
  ![!![0, -1, 0; -1, 0, -1; 0, 1, 1],
    !![-1, 0, -1; 0, -1, 0; 0, 1, 1],
    !![-1, 0, -1; 0, 1, 1; 0, -1, 0],
    !![-1, -1, -1; 0, -1, 0; 0, 1, 1],
    !![-1, -1, -1; 0, 1, 1; 0, -1, 0],
    !![-1, 0, -1; 0, 0, 1; 0, -1, 0]]

theorem gMat_mul_gInv (i : Fin 6) : gMat i * gInv i = 1 := by
  fin_cases i <;> decide

theorem gInv_mul_gMat (i : Fin 6) : gInv i * gMat i = 1 := by
  fin_cases i <;> decide

/-- The neighbour matrices as elements of `GL₃(ℤ)`. -/
def g0 (i : Fin 6) : IntegralGL3 := ⟨gMat i, gInv i, gMat_mul_gInv i, gInv_mul_gMat i⟩

theorem A0_add_U0 (i : Fin 6) : A0 + U0 i = act (g0 i) A0 := by
  ext a b
  simp only [act, toQ, g0, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [A0, U0, gMat, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

/-- The new minimal vector of the neighbour `A₀ + U₀ i`. -/
def mNew : Fin 6 → Vec :=
  ![![1, -1, -1], ![1, -1, 1], ![1, 1, -1], ![1, 1, -1], ![1, -1, 1], ![1, -1, -1]]

theorem Q0_mNew (i : Fin 6) : Q0 (mNew i) = 2 := by
  fin_cases i <;> decide

theorem qf_neighbour_mNew (i : Fin 6) : qf (A0 + U0 i) (mNew i) = 1 := by
  fin_cases i <;>
    norm_num [qf, A0, U0, mNew, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail]

/-- The coefficients of the rank-one relation at the facet opposite `m i`. -/
def relCoef : Fin 6 → Fin 6 → ℤ :=
  ![![0, 1, 1, 1, 1, -1], ![1, 0, 1, 1, -1, 1], ![1, 1, 0, -1, 1, 1],
    ![1, 1, -1, 0, 1, 1], ![1, -1, 1, 1, 0, 1], ![-1, 1, 1, 1, 1, 0]]

theorem relCoef_self (i : Fin 6) : relCoef i i = 0 := by
  fin_cases i <;> rfl

/-- The rank-one forms of the old and the new minimal vector agree modulo the others. -/
theorem rankOne_relation (i : Fin 6) :
    rankOne (mNew i) + rankOne (m i) = ∑ k, relCoef i k • rankOne (m k) := by
  fin_cases i <;> funext a <;> fin_cases a <;>
    simp [rankOne, mNew, m, relCoef, Fin.sum_univ_succ]

/-! ### Finite facts -/

theorem m_injective_mod (i k : Fin 6) (h : i ≠ k) :
    red (m k) ≠ red (m i) ∧ red (m k) ≠ -red (m i) := by
  revert i k
  decide

theorem red_m_ne_zero (i : Fin 6) : red (m i) ≠ 0 := by
  revert i
  decide

theorem red_mNew_ne_zero (i : Fin 6) : red (mNew i) ≠ 0 := by
  revert i
  decide

theorem pair_extends (i k : Fin 6) (h : i ≠ k) : ∃ l : Fin 6, det3v (m i) (m k) (m l) ≠ 0 := by
  revert i k
  decide

theorem span_rankOne_m :
    Submodule.span (ZMod 3) (Set.range fun k : Fin 6 => rankOne (red (m k))) = ⊤ := by
  set S := Submodule.span (ZMod 3) (Set.range fun k : Fin 6 => rankOne (red (m k)))
  have hk : ∀ k, rankOne (red (m k)) ∈ S := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hs : ∀ a : Fin 6, (fun j : Fin 6 => if a = j then (1 : ZMod 3) else 0) ∈ S := by
    intro a
    fin_cases a
    · convert hk 0 using 1
      decide
    · convert hk 1 using 1
      decide
    · convert hk 2 using 1
      decide
    · convert S.sub_mem (S.add_mem (hk 0) (hk 1)) (hk 3) using 1
      decide
    · convert S.sub_mem (S.add_mem (hk 0) (hk 2)) (hk 4) using 1
      decide
    · convert S.sub_mem (S.add_mem (hk 1) (hk 2)) (hk 5) using 1
      decide
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  exact S.sum_mem fun a _ => S.smul_mem _ (hs a)

end TernaryPeriodPolynomials.FreeResolution
