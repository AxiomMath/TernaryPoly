module

public import TernaryPeriodPolynomials.Building.FreeResolution.Vertices
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section


/-!
# Local finiteness of the vertices

Original work by Claude Opus 5.5.

In a basis `w₀, w₁, w₂` of `ℚ³` by integer vectors, the Gram matrix of a vertex has
half-integral entries (twice the bilinear form of `A₀` is integral), and it determines the
vertex. Hence only finitely many vertices have a bounded Gram matrix in a fixed basis. Two
consequences: a spanning set of lines is minimal for only finitely many vertices (in a basis taken
from the set the Gram matrix has unit diagonal, so its entries are at most one), and only finitely
many vertices have bounded trace.
-/

noncomputable section

namespace TernaryPeriodPolynomials.FreeResolution

open GeneralEisenstein Matrix

/-- The bilinear form of a Gram matrix on integer vectors. -/
def bil (A : Form) (u u' : Vec) : ℚ := ∑ i, ∑ j, A i j * (u i : ℚ) * (u' j : ℚ)

theorem bil_act (h : IntegralGL3) (A : Form) (u u' : Vec) :
    bil (act h A) u u' = bil A (mv h u) (mv h u') := by
  simp only [bil, act, toQ, mv, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Int.coe_castRingHom, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push_cast
  ring

/-- Twice the bilinear form of `A₀`, an integer. -/
def B0int (p q : Vec) : ℤ :=
  2 * p 0 * q 0 + 2 * p 1 * q 1 + 2 * p 2 * q 2 + p 0 * q 1 + p 1 * q 0 + p 0 * q 2 + p 2 * q 0 +
    p 1 * q 2 + p 2 * q 1

theorem two_bil_A0 (p q : Vec) : 2 * bil A0 p q = (B0int p q : ℚ) := by
  simp [bil, A0, B0int, Fin.sum_univ_three]
  ring

theorem two_bil_gram (v : Vtx) (u u' : Vec) :
    2 * bil v.gram u u' = (B0int (mv v.frame u) (mv v.frame u') : ℚ) := by
  rw [v.gram_eq, bil_act, two_bil_A0]

theorem Q0_nonneg (p : Vec) : 0 ≤ Q0 p := by
  have h := two_Q0 p
  nlinarith [sq_nonneg (p 0), sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 0 + p 1 + p 2)]

theorem Q0_add (p q : Vec) : Q0 (p + q) = Q0 p + Q0 q + B0int p q := by
  simp only [Q0, B0int, Pi.add_apply]
  ring

theorem Q0_sub (p q : Vec) : Q0 (p - q) = Q0 p + Q0 q - B0int p q := by
  simp only [Q0, B0int, Pi.sub_apply]
  ring

theorem abs_B0int_le (p q : Vec) : |B0int p q| ≤ Q0 p + Q0 q := by
  have h1 := Q0_nonneg (p + q)
  have h2 := Q0_nonneg (p - q)
  rw [Q0_add] at h1
  rw [Q0_sub] at h2
  rw [abs_le]
  constructor <;> linarith

theorem qf_gram_eq_Q0 (v : Vtx) (x : Vec) : qf v.gram x = (Q0 (mv v.frame x) : ℚ) := by
  rw [v.qf_gram, qf_A0]

/-- The rational matrix with integer rows `w i`. -/
def rowMat (w : Fin 3 → Vec) : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of fun i k => (w i k : ℚ)

theorem rowMat_mul_apply (w : Fin 3 → Vec) (A : Form) (i j : Fin 3) :
    (rowMat w * A * (rowMat w)ᵀ) i j = bil A (w i) (w j) := by
  simp only [rowMat, bil, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
    Fin.sum_univ_three]
  ring

theorem det_rowMat (w : Fin 3 → Vec) : (rowMat w).det = (det3v (w 0) (w 1) (w 2) : ℚ) := by
  simp only [rowMat, Matrix.det_fin_three, Matrix.of_apply, det3v]
  push_cast
  ring

/-- A form is determined by its Gram matrix in a basis. -/
theorem form_eq_of_bil (w : Fin 3 → Vec) (hw : det3v (w 0) (w 1) (w 2) ≠ 0) {A A' : Form}
    (h : ∀ i j, bil A (w i) (w j) = bil A' (w i) (w j)) : A = A' := by
  set P := rowMat w
  have hdet : IsUnit P.det := by
    rw [isUnit_iff_ne_zero, det_rowMat]
    exact_mod_cast hw
  have hdetT : IsUnit Pᵀ.det := by rwa [Matrix.det_transpose]
  have hG : P * A * Pᵀ = P * A' * Pᵀ := by
    ext i j
    rw [rowMat_mul_apply, rowMat_mul_apply, h]
  have key : ∀ B : Form, B = P⁻¹ * (P * B * Pᵀ) * Pᵀ⁻¹ := by
    intro B
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdetT, Matrix.mul_one]
  rw [key A, key A', hG]

/-- Only finitely many vertices have a bounded Gram matrix in a fixed integral basis. -/
theorem finite_of_bounded (w : Fin 3 → Vec) (hw : det3v (w 0) (w 1) (w 2) ≠ 0) (K : ℤ) :
    {v : Vtx | ∀ i j, |B0int (mv v.frame (w i)) (mv v.frame (w j))| ≤ K}.Finite := by
  let ψ : Vtx → Fin 3 → Fin 3 → ℤ := fun v i j => B0int (mv v.frame (w i)) (mv v.frame (w j))
  have hinj : Function.Injective ψ := by
    intro v v' hvv
    apply Vtx.ext
    apply form_eq_of_bil w hw
    intro i j
    have e1 := two_bil_gram v (w i) (w j)
    have e2 := two_bil_gram v' (w i) (w j)
    have e3 : B0int (mv v.frame (w i)) (mv v.frame (w j)) =
        B0int (mv v'.frame (w i)) (mv v'.frame (w j)) := congrFun (congrFun hvv i) j
    rw [e3] at e1
    linarith
  have hfin : (Set.range fun N : Fin 3 → Fin 3 → Finset.Icc (-K) K =>
      fun i j => ((N i j : ℤ))).Finite := Set.finite_range _
  refine Set.Finite.of_finite_image (f := ψ) (hfin.subset ?_) hinj.injOn
  rintro _ ⟨v, hv, rfl⟩
  have hv' : ∀ i j, |B0int (mv v.frame (w i)) (mv v.frame (w j))| ≤ K := hv
  exact ⟨fun i j => ⟨ψ v i j, Finset.mem_Icc.mpr (abs_le.mp (hv' i j))⟩, rfl⟩

/-- The vertices whose minimal lines contain `T`. -/
def vertSet (T : Finset Line) : Set Vtx := {v | T ⊆ v.M}

theorem qf_out_of_mem (v : Vtx) {a : Line} (ha : a ∈ v.M) :
    Q0 (mv v.frame (Quotient.out a)) = 1 := by
  have h := (v.mem_M a).mp ha
  rw [← Line.mk_out a, Line.qf_mk, qf_gram_eq_Q0] at h
  exact_mod_cast h

/-- A spanning set of lines is minimal for only finitely many vertices. -/
theorem vertSet_finite {T : Finset Line} (hT : Spans T) : (vertSet T).Finite := by
  obtain ⟨a, ha, b, hb, c, hc, habc⟩ := hT
  let w : Fin 3 → Vec := ![Quotient.out a, Quotient.out b, Quotient.out c]
  have hw : det3v (w 0) (w 1) (w 2) ≠ 0 := habc
  refine (finite_of_bounded w hw 2).subset ?_
  intro v hv
  have hv' : T ⊆ v.M := hv
  have hQ : ∀ i, Q0 (mv v.frame (w i)) = 1 := by
    intro i
    fin_cases i
    · exact qf_out_of_mem v (hv' ha)
    · exact qf_out_of_mem v (hv' hb)
    · exact qf_out_of_mem v (hv' hc)
  show ∀ i j, |B0int (mv v.frame (w i)) (mv v.frame (w j))| ≤ _
  intro i j
  have := abs_B0int_le (mv v.frame (w i)) (mv v.frame (w j))
  rw [hQ i, hQ j] at this
  simpa using this

/-- The trace of a vertex. -/
def Vtx.trace (v : Vtx) : ℚ := v.gram 0 0 + v.gram 1 1 + v.gram 2 2

theorem gram_diag (v : Vtx) (i : Fin 3) :
    v.gram i i = (Q0 (mv v.frame (Pi.single i 1)) : ℚ) := by
  rw [← qf_gram_eq_Q0]
  fin_cases i <;> simp [qf, Pi.single_apply]

/-- Only finitely many vertices have bounded trace. -/
theorem trace_finite (c : ℚ) : {v : Vtx | v.trace ≤ c}.Finite := by
  let w : Fin 3 → Vec := fun i => Pi.single i 1
  have hw : det3v (w 0) (w 1) (w 2) ≠ 0 := by decide
  refine (finite_of_bounded w hw (2 * ⌈c⌉)).subset ?_
  intro v hv
  have hv' : v.trace ≤ c := hv
  have hQ : ∀ i, (Q0 (mv v.frame (w i)) : ℚ) = v.gram i i := fun i => (gram_diag v i).symm
  have hn : ∀ i, 0 ≤ Q0 (mv v.frame (w i)) := fun i => Q0_nonneg _
  have hsum : ∑ k, Q0 (mv v.frame (w k)) ≤ ⌈c⌉ := by
    have h1 : ((∑ k, Q0 (mv v.frame (w k)) : ℤ) : ℚ) ≤ c := by
      push_cast
      simp only [hQ, Fin.sum_univ_three]
      exact hv'
    exact Int.cast_le.mp (le_trans h1 (Int.le_ceil c))
  have hle : ∀ i, Q0 (mv v.frame (w i)) ≤ ⌈c⌉ := fun i =>
    le_trans (Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)) hsum
  show ∀ i j, |B0int (mv v.frame (w i)) (mv v.frame (w j))| ≤ _
  intro i j
  have h1 := abs_B0int_le (mv v.frame (w i)) (mv v.frame (w j))
  have hi := hle i
  have hj := hle j
  linarith

end TernaryPeriodPolynomials.FreeResolution
