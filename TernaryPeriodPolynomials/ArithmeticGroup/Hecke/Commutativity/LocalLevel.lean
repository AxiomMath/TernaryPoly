module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.CosetDecomposition
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.LevelIntersection
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.Involution
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Commutativity.ShimuraCount

@[expose] public section


/-!
# Local description of the level and a local–global principle for double cosets

`LocK x v` says that the rational matrix `x` lies in the local component of the
level at the finite place `v`: `x` and `x⁻¹` are `v`-integral and, at `v = 3`,
the last row of `x` is `e₃*` modulo three.

* `mem_rationalLevel_of_locK`: `x ∈ rationalLevel` iff `LocK x v` for every `v`.
* `ofLocal`: a family of rational matrices, each in the local level at its own
  place, defines an element of `finiteLevel` with the prescribed components.
* `mem_dcoset_of_finite`: if `y = k x k'` adelically with `k, k' ∈ finiteLevel`
  then `y ∈ Γ x Γ` (strong approximation, via `cosetDecomposition_all`).

Original work (AxiomDeep, Claude Opus 5.5).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic Matrix IsDedekindDomain

namespace TernaryPeriodPolynomials.HeckeCommutativity

/-- A rational number integral at the place `v`. -/
def IntAt (v : FinitePlace) (q : ℚ) : Prop :=
  algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ

theorem intAt_add {v : FinitePlace} {p q : ℚ} (hp : IntAt v p) (hq : IntAt v q) :
    IntAt v (p + q) := by
  unfold IntAt at *
  rw [map_add]
  exact add_mem hp hq

theorem intAt_mul {v : FinitePlace} {p q : ℚ} (hp : IntAt v p) (hq : IntAt v q) :
    IntAt v (p * q) := by
  unfold IntAt at *
  rw [map_mul]
  exact mul_mem hp hq

theorem intAt_neg {v : FinitePlace} {p : ℚ} (hp : IntAt v p) : IntAt v (-p) := by
  unfold IntAt at *
  rw [map_neg]
  exact neg_mem hp

theorem intAt_sub {v : FinitePlace} {p q : ℚ} (hp : IntAt v p) (hq : IntAt v q) :
    IntAt v (p - q) := by
  rw [sub_eq_add_neg]
  exact intAt_add hp (intAt_neg hq)

theorem intAt_intCast (v : FinitePlace) (z : ℤ) : IntAt v (z : ℚ) := by
  unfold IntAt
  rw [map_intCast]
  exact intCast_mem _ z

theorem intAt_one (v : FinitePlace) : IntAt v 1 := by
  simpa using intAt_intCast v 1

theorem intAt_zero (v : FinitePlace) : IntAt v 0 := by
  simpa using intAt_intCast v 0

theorem intAt_sum {v : FinitePlace} {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (h : ∀ i ∈ s, IntAt v (f i)) : IntAt v (∑ i ∈ s, f i) := by
  unfold IntAt at *
  rw [map_sum]
  exact sum_mem h

/-- The local component of the level at `v`. -/
def LocK (x : RationalGL3) (v : FinitePlace) : Prop :=
  (∀ i j, IntAt v (x.val i j)) ∧ (∀ i j, IntAt v ((x⁻¹).val i j)) ∧
    (v = placeThree → ∀ j, IntAt v ((x.val 2 j - if j = 2 then 1 else 0) / 3))

theorem intAt_mat_mul {v : FinitePlace} {A B : Matrix (Fin 3) (Fin 3) ℚ}
    (hA : ∀ i j, IntAt v (A i j)) (hB : ∀ i j, IntAt v (B i j)) :
    ∀ i j, IntAt v ((A * B) i j) := by
  intro i j
  rw [Matrix.mul_apply]
  exact intAt_sum _ _ (fun k _ => intAt_mul (hA i k) (hB k j))

theorem row_mul_identity (A B : Matrix (Fin 3) (Fin 3) ℚ) (j : Fin 3) :
    ((A * B) 2 j - if j = 2 then 1 else 0) / 3 =
      ∑ k, ((A 2 k - if k = 2 then 1 else 0) / 3) * B k j +
        (B 2 j - if j = 2 then 1 else 0) / 3 := by
  simp only [Matrix.mul_apply, Fin.sum_univ_three]
  fin_cases j <;> simp <;> ring

theorem locK_mul {x y : RationalGL3} {v : FinitePlace} (hx : LocK x v) (hy : LocK y v) :
    LocK (x * y) v := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul]
    exact intAt_mat_mul hx.1 hy.1
  · rw [_root_.mul_inv_rev, Units.val_mul]
    exact intAt_mat_mul hy.2.1 hx.2.1
  · intro hv j
    rw [Units.val_mul, row_mul_identity]
    exact intAt_add (intAt_sum _ _ (fun k _ => intAt_mul (hx.2.2 hv k) (hy.1 k j))) (hy.2.2 hv j)

theorem row_inv_identity (x : RationalGL3) (j : Fin 3) :
    (((x⁻¹).val 2 j - if j = 2 then 1 else 0) / 3) =
      -∑ k, ((x.val 2 k - if k = 2 then 1 else 0) / 3) * (x⁻¹).val k j := by
  have h := congrFun (congrFun (Units.mul_inv x) 2) j
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply] at h
  simp only [Fin.sum_univ_three]
  fin_cases j <;> simp at h ⊢ <;> linear_combination (1 / 3 : ℚ) * h

theorem locK_inv {x : RationalGL3} {v : FinitePlace} (hx : LocK x v) : LocK x⁻¹ v := by
  refine ⟨hx.2.1, ?_, ?_⟩
  · rw [inv_inv]
    exact hx.1
  · intro hv j
    rw [row_inv_identity]
    exact intAt_neg (intAt_sum _ _ (fun k _ => intAt_mul (hx.2.2 hv k) (hx.2.1 k j)))

theorem locK_one (v : FinitePlace) : LocK 1 v := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun _ j => ?_⟩
  · rw [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact intAt_one v
    · exact intAt_zero v
  · rw [inv_one, Units.val_one, Matrix.one_apply]
    split_ifs
    · exact intAt_one v
    · exact intAt_zero v
  · rw [Units.val_one, Matrix.one_apply]
    fin_cases j <;> simpa using intAt_zero v

theorem locK_of_mem {γ : RationalGL3} (hγ : γ ∈ rationalLevel) (v : FinitePlace) : LocK γ v := by
  obtain ⟨M, hM, -, hrow⟩ := int_of_mem_rationalLevel hγ
  obtain ⟨M', hM', -, -⟩ := int_of_mem_rationalLevel (inv_mem hγ)
  refine ⟨fun i j => ?_, fun i j => ?_, fun _ j => ?_⟩
  · rw [hM, Matrix.map_apply]
    exact intAt_intCast v _
  · rw [hM', Matrix.map_apply]
    exact intAt_intCast v _
  · have h3 : (3 : ℤ) ∣ M 2 j - if j = 2 then 1 else 0 := by
      have := hrow j
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
      push_cast
      rw [this]
      split_ifs <;> simp
    obtain ⟨k, hk⟩ := h3
    have : ((γ.val 2 j - if j = 2 then 1 else 0) / 3 : ℚ) = (k : ℚ) := by
      rw [hM, Matrix.map_apply]
      have hk' : ((M 2 j : ℤ) : ℚ) - ((if j = 2 then 1 else 0 : ℤ) : ℚ) = 3 * k := by
        exact_mod_cast hk
      split_ifs at hk' ⊢ <;> push_cast at hk' <;> linarith
    rw [this]
    exact intAt_intCast v k

theorem locK_of_dcoset {x y : RationalGL3} (hy : y ∈ dcoset rationalLevel x) {v : FinitePlace}
    (hx : LocK x v) : LocK y v := by
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy
  exact locK_mul (locK_mul (locK_of_mem hh₁ v) hx) (locK_of_mem hh₂ v)

end TernaryPeriodPolynomials.HeckeCommutativity
