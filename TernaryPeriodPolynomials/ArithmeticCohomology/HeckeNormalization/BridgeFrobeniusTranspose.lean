module

public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermEval

@[expose] public section


/-!
# Transposition of locally finite twisted endomorphisms of a permutation module (L2, generic part)

Formalized by Claude Sonnet 5.5.  Supports the Hecke bridge B1.

For a set `X` with the standard symmetric pairing `pairX u v = ∑_x u_x v_x` on `ℚ[X]`:
* `pairX` is bilinear, symmetric, nondegenerate on the basis (`eq_of_pairX`), and invariant under `ofMulAction` (`pairX_invariant`,
  `pairX_ρ_left`);
* `matX s x y` is the matrix of an endomorphism `s` of `ℚ[X]`; if `s (f σ · w) = σ · s w` for `σ ∈ S` (`f : S →* Γ`), `X` has finite
  stabilizers and finitely many `f(S)`-orbits, every column of `matX s` is finitely supported (`matX_col_finite`; the finite support
  of the rows is automatic, the columns need the orbit/stabilizer count);
* `exists_transpose`: then `s` has a transpose `l` (`pairX (l u) v = pairX u (s v)`) with `l (σ · w) = f σ · l w`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

open CategoryTheory Representation Rep
open TernaryPeriodPolynomials.Argument.BinaryDuality
open scoped Classical MonoidAlgebra

section Pairing

variable {X : Type}

/-- The standard symmetric pairing on `ℚ[X]`: `⟨u, v⟩ = ∑_x u_x v_x`. -/
def pairX (u v : MonoidAlgebra ℚ X) : ℚ := u.coeff.sum fun x a => a * v.coeff x

theorem pairX_add_left (u u' v : MonoidAlgebra ℚ X) : pairX (u + u') v = pairX u v + pairX u' v := by
  unfold pairX
  rw [MonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index' (fun a => zero_mul _) (fun a b c => add_mul _ _ _)

theorem pairX_add_right (u v v' : MonoidAlgebra ℚ X) : pairX u (v + v') = pairX u v + pairX u v' := by
  unfold pairX
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

theorem pairX_zero_left (v : MonoidAlgebra ℚ X) : pairX 0 v = 0 := by
  unfold pairX; simp

theorem pairX_zero_right (u : MonoidAlgebra ℚ X) : pairX u 0 = 0 := by
  unfold pairX; simp

theorem pairX_smul_left (c : ℚ) (u v : MonoidAlgebra ℚ X) : pairX (c • u) v = c * pairX u v := by
  unfold pairX
  have : (c • u).coeff = c • u.coeff := rfl
  rw [this, Finsupp.sum_smul_index' (fun x => zero_mul _), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [smul_eq_mul, mul_assoc]

theorem pairX_smul_right (c : ℚ) (u v : MonoidAlgebra ℚ X) : pairX u (c • v) = c * pairX u v := by
  unfold pairX
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  have : (c • v).coeff x = c * v.coeff x := rfl
  rw [this]; ring

theorem pairX_single_left (x : X) (r : ℚ) (v : MonoidAlgebra ℚ X) :
    pairX (MonoidAlgebra.single x r) v = r * v.coeff x := by
  unfold pairX
  rw [MonoidAlgebra.coeff_single, Finsupp.sum_single_index (zero_mul _)]

theorem pairX_single_single (x y : X) (r q : ℚ) :
    pairX (MonoidAlgebra.single x r) (MonoidAlgebra.single y q) = if x = y then r * q else 0 := by
  rw [pairX_single_left, MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : y = x
  · subst h; simp
  · simp [h, Ne.symm h]

theorem pairX_comm (u v : MonoidAlgebra ℚ X) : pairX u v = pairX v u := by
  induction u using MonoidAlgebra.induction_linear with
  | zero => rw [pairX_zero_left, pairX_zero_right]
  | add a b ha hb => rw [pairX_add_left, pairX_add_right, ha, hb]
  | single x r =>
    induction v using MonoidAlgebra.induction_linear with
    | zero => rw [pairX_zero_left, pairX_zero_right]
    | add a b ha hb => rw [pairX_add_left, pairX_add_right, ha, hb]
    | single y q =>
      rw [pairX_single_single, pairX_single_single]
      by_cases h : x = y
      · subst h; simp [mul_comm]
      · simp [h, Ne.symm h]

theorem pairX_single_right (u : MonoidAlgebra ℚ X) (x : X) (r : ℚ) :
    pairX u (MonoidAlgebra.single x r) = u.coeff x * r := by
  rw [pairX_comm, pairX_single_left, mul_comm]

theorem eq_of_pairX {u w : MonoidAlgebra ℚ X} (h : ∀ x, pairX u (MonoidAlgebra.single x 1) = pairX w (MonoidAlgebra.single x 1)) :
    u = w := by
  apply MonoidAlgebra.coeff_injective
  ext x
  have := h x
  rw [pairX_single_right, pairX_single_right] at this
  simpa using this

variable {Γ : Type} [Group Γ] [MulAction Γ X]

theorem pairX_invariant (γ : Γ) (u v : MonoidAlgebra ℚ X) :
    pairX (Representation.ofMulAction ℚ Γ X γ u) (Representation.ofMulAction ℚ Γ X γ v) = pairX u v := by
  induction u using MonoidAlgebra.induction_linear with
  | zero => rw [map_zero, pairX_zero_left, pairX_zero_left]
  | add a b ha hb => rw [map_add, pairX_add_left, pairX_add_left, ha, hb]
  | single x r =>
    induction v using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, pairX_zero_right, pairX_zero_right]
    | add a b ha hb => rw [map_add, pairX_add_right, pairX_add_right, ha, hb]
    | single y q =>
      rw [Representation.ofMulAction_single, Representation.ofMulAction_single, pairX_single_single,
        pairX_single_single]
      by_cases h : x = y
      · subst h; simp
      · have : γ • x ≠ γ • y := fun h' => h (MulAction.injective γ h')
        simp [h, this]

end Pairing

section Transpose

variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X] (S : Subgroup Γ) (f : S →* Γ)

theorem coeff_ofMulAction (γ : Γ) (w : MonoidAlgebra ℚ X) (y : X) :
    (Representation.ofMulAction ℚ Γ X γ w).coeff (γ • y) = w.coeff y := by
  simp

/-- The matrix of an endomorphism of `ℚ[X]` in the basis `X`: `s [x] = ∑_y mat s x y [y]`. -/
def matX (s : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X) (x y : X) : ℚ :=
  (s (MonoidAlgebra.single x (1 : ℚ))).coeff y

variable {S f}

theorem matX_twisted {s : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X}
    (hs : ∀ (σ : S) (w : MonoidAlgebra ℚ X),
      s (Representation.ofMulAction ℚ Γ X (f σ) w) = Representation.ofMulAction ℚ Γ X σ.1 (s w))
    (σ : S) (x y : X) : matX s (f σ • x) (σ.1 • y) = matX s x y := by
  unfold matX
  rw [← Representation.ofMulAction_single (f σ) x (1 : ℚ), hs, coeff_ofMulAction]

/-- **Finiteness of the columns**: for an `f`-twisted `S`-equivariant `s` with finitely many `f(S)`-orbits on `X`
and finite stabilizers, each column of the matrix of `s` is finitely supported. -/
theorem matX_col_finite {s : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X}
    (hs : ∀ (σ : S) (w : MonoidAlgebra ℚ X),
      s (Representation.ofMulAction ℚ Γ X (f σ) w) = Representation.ofMulAction ℚ Γ X σ.1 (s w))
    (hX : ∀ x : X, Finite (MulAction.stabilizer Γ x))
    (hI : ∃ I : Set X, I.Finite ∧ ∀ x, ∃ i ∈ I, ∃ σ : S, x = f σ • i) (y : X) :
    (Function.support fun x => matX s x y).Finite := by
  obtain ⟨I, hIf, hIc⟩ := hI
  have hfin : ∀ y'' : X, {σ : S | σ.1 • y'' = y}.Finite := fun y'' => by
    have := Set.Finite.preimage (f := (Subtype.val : S → Γ)) Subtype.val_injective.injOn (transp_finite (Γ := Γ) (hX y) y'')
    exact this
  refine Set.Finite.subset (hIf.biUnion fun i _ => ((s (MonoidAlgebra.single i (1 : ℚ))).coeff.support.finite_toSet.biUnion
    fun y'' _ => (hfin y'').image (fun σ : S => f σ • i))) ?_
  intro x hx
  obtain ⟨i, hi, σ, rfl⟩ := hIc x
  simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Finsupp.mem_support_iff, exists_prop]
  refine ⟨i, hi, σ⁻¹.1 • y, ?_, σ, ?_, rfl⟩
  · have h := matX_twisted hs σ i (σ⁻¹.1 • y)
    have e : σ.1 • σ⁻¹.1 • y = y := by
      rw [← mul_smul]; simp
    rw [e] at h
    have hx' : matX s (f σ • i) y ≠ 0 := hx
    rw [h] at hx'
    exact hx'
  · show σ.1 • σ⁻¹.1 • y = y
    rw [← mul_smul]; simp

theorem pairX_ρ_left (γ : Γ) (a b : MonoidAlgebra ℚ X) :
    pairX (Representation.ofMulAction ℚ Γ X γ a) b = pairX a (Representation.ofMulAction ℚ Γ X γ⁻¹ b) := by
  have h : Representation.ofMulAction ℚ Γ X γ (Representation.ofMulAction ℚ Γ X γ⁻¹ b) = b := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  conv_lhs => rw [← h]
  rw [pairX_invariant]

/-- **Transposition of locally finite twisted maps.**  Let `s` be an endomorphism of `ℚ[X]` with
`s (f σ · w) = σ · s w` for `σ ∈ S`, where `X` has finite stabilizers and finitely many `f(S)`-orbits.  Then `s` has a
transpose `l` for the standard pairing, and `l (σ · w) = f σ · l w`. -/
theorem exists_transpose {s : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X}
    (hs : ∀ (σ : S) (w : MonoidAlgebra ℚ X),
      s (Representation.ofMulAction ℚ Γ X (f σ) w) = Representation.ofMulAction ℚ Γ X σ.1 (s w))
    (hX : ∀ x : X, Finite (MulAction.stabilizer Γ x))
    (hI : ∃ I : Set X, I.Finite ∧ ∀ x, ∃ i ∈ I, ∃ σ : S, x = f σ • i) :
    ∃ l : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X,
      (∀ u v, pairX (l u) v = pairX u (s v)) ∧
      ∀ (σ : S) (w : MonoidAlgebra ℚ X),
        l (Representation.ofMulAction ℚ Γ X σ.1 w) = Representation.ofMulAction ℚ Γ X (f σ) (l w) := by
  let colF : X → (X →₀ ℚ) := fun y => Finsupp.ofSupportFinite (fun x => matX s x y) (matX_col_finite hs hX hI y)
  let l : MonoidAlgebra ℚ X →ₗ[ℚ] MonoidAlgebra ℚ X :=
    (MonoidAlgebra.coeffLinearEquiv ℚ).symm.toLinearMap ∘ₗ Finsupp.linearCombination ℚ colF ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap
  have hl : ∀ (y x : X) (r : ℚ), (l (MonoidAlgebra.single y r)).coeff x = r * matX s x y := by
    intro y x r
    change (Finsupp.linearCombination ℚ colF (Finsupp.single y r)) x = _
    rw [Finsupp.linearCombination_single]
    rfl
  have hadj : ∀ u v, pairX (l u) v = pairX u (s v) := by
    intro u v
    induction u using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero, pairX_zero_left, pairX_zero_left]
    | add a b ha hb => rw [map_add, pairX_add_left, pairX_add_left, ha, hb]
    | single y r =>
      induction v using MonoidAlgebra.induction_linear with
      | zero => rw [pairX_zero_right, map_zero, pairX_zero_right]
      | add a b ha hb => rw [pairX_add_right, map_add, pairX_add_right, ha, hb]
      | single x q =>
        rw [pairX_single_right, hl, pairX_single_left]
        have : (MonoidAlgebra.single x q : MonoidAlgebra ℚ X) = q • MonoidAlgebra.single x (1 : ℚ) := by
          rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
        rw [this, map_smul]
        change r * matX s x y * q = r * (q * matX s x y)
        ring
  refine ⟨l, hadj, fun σ w => ?_⟩
  apply eq_of_pairX
  intro x
  rw [hadj, pairX_ρ_left (f σ), hadj]
  have hinv : Representation.ofMulAction ℚ Γ X ((f σ)⁻¹) (MonoidAlgebra.single x (1 : ℚ)) =
      Representation.ofMulAction ℚ Γ X (f σ⁻¹) (MonoidAlgebra.single x (1 : ℚ)) := by rw [map_inv f σ]
  rw [hinv, hs σ⁻¹, pairX_ρ_left]
  rfl

end Transpose

end TernaryPeriodPolynomials.Argument.HeckeNormalization
