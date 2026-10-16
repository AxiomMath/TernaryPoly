module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.PermProjective
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.Order.Fin.SuccAboveOrderIso

@[expose] public section


/-!
# Evaluation of coinvariants of permutation modules at a base point

Formalized by Claude Sonnet 5.5.

For a `Γ`-set `X` with a base point `x₀` of finite stabilizer and a `ℚ`-representation `M`, the coinvariants
`(M ⊗ ℚ[X])_Γ` map to `M` by `[m ⊗ y] ↦ ∑_{γ y = x₀} γ m` (`evalAt`; the sum over the coset of group elements carrying
`y` to `x₀`).  If `Γ` is transitive on `X` this is injective (`evalAt_injective`) with image the `Stab x₀`-invariants
(`mem_range_evalAt`): the norm isomorphism `(M ⊗ ℚ[Γ/S])_Γ ≅ M^S` in characteristic zero.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.BinaryDuality

open CategoryTheory Representation Rep
open scoped Classical MonoidAlgebra

variable {Γ : Type} [Group Γ] {X : Type} [MulAction Γ X]

/-- The group elements carrying `y` to the base point `x₀`. -/
def transp (x₀ y : X) : Set Γ := {γ | γ • y = x₀}

theorem transp_smul (x₀ y : X) (g : Γ) :
    transp (Γ := Γ) x₀ (g • y) = (fun γ => γ * g⁻¹) '' transp x₀ y := by
  ext γ
  simp only [transp, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro h
    exact ⟨γ * g, by rw [mul_smul]; exact h, mul_inv_cancel_right γ g⟩
  · rintro ⟨δ, hδ, rfl⟩
    rw [mul_smul, inv_smul_smul]
    exact hδ

theorem transp_finite {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (y : X) :
    (transp (Γ := Γ) x₀ y).Finite := by
  by_cases h : (transp (Γ := Γ) x₀ y).Nonempty
  · obtain ⟨γ₁, hγ₁⟩ := h
    have : transp (Γ := Γ) x₀ y ⊆ (fun s => s * γ₁) '' (MulAction.stabilizer Γ x₀ : Set Γ) := by
      intro γ hγ
      refine ⟨γ * γ₁⁻¹, ?_, inv_mul_cancel_right γ γ₁⟩
      simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
      have h1 : γ • y = x₀ := hγ
      have h2 : γ₁ • y = x₀ := hγ₁
      have h3 : γ₁⁻¹ • x₀ = y := by rw [← h2, inv_smul_smul]
      rw [mul_smul, h3, h1]
    exact (Set.Finite.image _ (Set.toFinite _)).subset this
  · rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h]; exact Set.finite_empty

/-- The sum over the group elements carrying `y` to the base point. -/
def normAt {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (y : X) : M →ₗ[ℚ] M :=
  ∑ γ ∈ (transp_finite hx₀ y).toFinset, M.ρ γ

theorem normAt_smul {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (y : X)
    (g : Γ) (m : M) : normAt hx₀ M (g • y) (M.ρ g m) = normAt hx₀ M y m := by
  unfold normAt
  have hset : (transp_finite hx₀ (g • y)).toFinset =
      (transp_finite hx₀ y).toFinset.image (fun γ => γ * g⁻¹) := by
    ext γ
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, transp_smul, Set.mem_image]
  rw [hset, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

/-- The evaluation `m ⊗ c ↦ ∑_y c(y) ∑_{γ y = x₀} γ m` on the tensor product. -/
def evalTen {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) :
    TensorProduct ℚ M (MonoidAlgebra ℚ X) →ₗ[ℚ] M :=
  TensorProduct.lift
    ((Finsupp.linearCombination ℚ (fun y => normAt hx₀ M y) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap).flip)

theorem evalTen_tmul_single {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ)
    (m : M) (y : X) (r : ℚ) :
    evalTen hx₀ M (m ⊗ₜ MonoidAlgebra.single y r) = r • normAt hx₀ M y m := by
  simp [evalTen]

theorem evalTen_invariant {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (g : Γ) :
    evalTen hx₀ M ∘ₗ (M.ρ.tprod (Rep.ofMulAction ℚ Γ X).ρ) g = evalTen hx₀ M := by
  apply TensorProduct.ext'
  intro m c
  induction c using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [TensorProduct.tmul_add, map_add, map_add, ha, hb]
  | single y r =>
    simp only [LinearMap.comp_apply, Representation.tprod_apply, TensorProduct.map_tmul]
    rw [Representation.ofMulAction_single, evalTen_tmul_single, evalTen_tmul_single, normAt_smul]

/-- Evaluation at the base point on the coinvariants `(M ⊗ ℚ[X])_Γ`. -/
def evalAt {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) :
    Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) →ₗ[ℚ] M :=
  Coinvariants.lift _ (evalTen hx₀ M) (evalTen_invariant hx₀ M)

theorem evalAt_mk {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (m : M)
    (c : MonoidAlgebra ℚ X) :
    evalAt hx₀ M (Coinvariants.mk _ (m ⊗ₜ c)) = evalTen hx₀ M (m ⊗ₜ c) := rfl

theorem transp_base (x₀ : X) : transp (Γ := Γ) x₀ x₀ = (MulAction.stabilizer Γ x₀ : Set Γ) := by
  ext γ; simp [transp, MulAction.mem_stabilizer_iff]

/-- The sum over the stabilizer of the base point. -/
def normStab {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) : M →ₗ[ℚ] M :=
  normAt hx₀ M x₀

theorem normStab_apply {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (m : M)
    (s : MulAction.stabilizer Γ x₀) : M.ρ s (normStab hx₀ M m) = normStab hx₀ M m := by
  unfold normStab normAt
  rw [LinearMap.sum_apply, map_sum]
  have hset : (transp_finite hx₀ x₀).toFinset.image (fun γ => (s : Γ) * γ) =
      (transp_finite hx₀ x₀).toFinset := by
    ext γ
    simp only [Finset.mem_image, Set.Finite.mem_toFinset, transp_base, SetLike.mem_coe]
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      exact (MulAction.stabilizer Γ x₀).mul_mem s.2 hδ
    · intro hγ
      exact ⟨(s : Γ)⁻¹ * γ, (MulAction.stabilizer Γ x₀).mul_mem ((MulAction.stabilizer Γ x₀).inv_mem s.2) hγ,
        mul_inv_cancel_left _ _⟩
  conv_rhs => rw [← hset]
  rw [Finset.sum_image (fun a _ b _ h => mul_left_cancel h)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Module.End.mul_apply, ← map_mul]

section Transitive

variable {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ)

/-- The generating map `m ↦ [m ⊗ [x₀]]`. -/
def genAt : M →ₗ[ℚ] Coinvariants ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) :=
  (Coinvariants.mk _) ∘ₗ ((TensorProduct.mk ℚ M (MonoidAlgebra ℚ X)).flip
    (MonoidAlgebra.single x₀ (1 : ℚ)))

theorem genAt_apply (m : M) :
    genAt (x₀ := x₀) M m = Coinvariants.mk _ (m ⊗ₜ MonoidAlgebra.single x₀ (1 : ℚ)) := rfl

theorem genAt_surjective (htr : ∀ y : X, ∃ γ : Γ, γ • x₀ = y) :
    Function.Surjective (genAt (x₀ := x₀) M) := by
  have hrange : LinearMap.range (genAt (x₀ := x₀) M) = ⊤ := by
    rw [eq_top_iff]
    intro w _
    obtain ⟨t, rfl⟩ := Coinvariants.mk_surjective _ w
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ (ha trivial) (hb trivial)
    | tmul m c =>
      induction c using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ (ha trivial) (hb trivial)
      | single y r =>
        obtain ⟨γ, rfl⟩ := htr y
        refine ⟨r • M.ρ γ⁻¹ m, ?_⟩
        rw [genAt_apply, TensorProduct.smul_tmul, MonoidAlgebra.smul_single, smul_eq_mul, mul_one,
          Coinvariants.mk_inv_tmul, Representation.ofMulAction_single]
  intro w
  have : w ∈ LinearMap.range (genAt (x₀ := x₀) M) := by rw [hrange]; trivial
  exact this

theorem evalAt_genAt (m : M) : evalAt hx₀ M (genAt (x₀ := x₀) M m) = normStab hx₀ M m := by
  rw [genAt_apply, evalAt_mk, evalTen_tmul_single, one_smul]; rfl

theorem genAt_stab (s : MulAction.stabilizer Γ x₀) (m : M) :
    genAt (x₀ := x₀) M (M.ρ s m) = genAt (x₀ := x₀) M m := by
  rw [genAt_apply, genAt_apply]
  have := Coinvariants.mk_self_apply ((M.ρ).tprod (Rep.ofMulAction ℚ Γ X).ρ) (s : Γ)
    (m ⊗ₜ MonoidAlgebra.single x₀ (1 : ℚ))
  rw [Representation.tprod_apply, TensorProduct.map_tmul, Representation.ofMulAction_single,
    (MulAction.mem_stabilizer_iff.mp s.2)] at this
  exact this

theorem card_smul_genAt (m : M) :
    (transp_finite hx₀ x₀).toFinset.card • genAt (x₀ := x₀) M m = genAt (x₀ := x₀) M (normStab hx₀ M m) := by
  unfold normStab normAt
  rw [LinearMap.sum_apply, map_sum, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  have hγ' : γ ∈ MulAction.stabilizer Γ x₀ := by
    have := (Set.Finite.mem_toFinset _).mp hγ
    rw [transp_base] at this
    exact this
  exact (genAt_stab M ⟨γ, hγ'⟩ m).symm

theorem evalAt_injective (htr : ∀ y : X, ∃ γ : Γ, γ • x₀ = y) :
    Function.Injective (evalAt hx₀ M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨m, rfl⟩ := genAt_surjective M htr w
  rw [evalAt_genAt] at hw
  have h := card_smul_genAt hx₀ M m
  rw [hw, map_zero] at h
  have hpos : (transp_finite hx₀ x₀).toFinset.card ≠ 0 := by
    apply Finset.card_ne_zero_of_mem (a := 1)
    rw [Set.Finite.mem_toFinset, transp_base]
    exact (MulAction.stabilizer Γ x₀).one_mem
  rw [← Nat.cast_smul_eq_nsmul ℚ] at h
  exact (smul_eq_zero.mp h).resolve_left (by exact_mod_cast hpos)

theorem mem_range_evalAt (htr : ∀ y : X, ∃ γ : Γ, γ • x₀ = y) (m : M) :
    m ∈ LinearMap.range (evalAt hx₀ M) ↔ ∀ s : MulAction.stabilizer Γ x₀, M.ρ s m = m := by
  constructor
  · rintro ⟨w, rfl⟩ s
    obtain ⟨m', rfl⟩ := genAt_surjective M htr w
    rw [evalAt_genAt]
    exact normStab_apply hx₀ M m' s
  · intro h
    have hpos : ((transp_finite hx₀ x₀).toFinset.card : ℚ) ≠ 0 := by
      have : (transp_finite hx₀ x₀).toFinset.card ≠ 0 := by
        apply Finset.card_ne_zero_of_mem (a := 1)
        rw [Set.Finite.mem_toFinset, transp_base]
        exact (MulAction.stabilizer Γ x₀).one_mem
      exact_mod_cast this
    refine ⟨((transp_finite hx₀ x₀).toFinset.card : ℚ)⁻¹ • genAt (x₀ := x₀) M m, ?_⟩
    rw [map_smul, evalAt_genAt]
    have : normStab hx₀ M m = ((transp_finite hx₀ x₀).toFinset.card : ℚ) • m := by
      unfold normStab normAt
      rw [LinearMap.sum_apply]
      have : ∀ γ ∈ (transp_finite hx₀ x₀).toFinset, M.ρ γ m = m := by
        intro γ hγ
        have hγ' : γ ∈ MulAction.stabilizer Γ x₀ := by
          have := (Set.Finite.mem_toFinset _).mp hγ
          rw [transp_base] at this
          exact this
        exact h ⟨γ, hγ'⟩
      rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.cast_smul_eq_nsmul]
    rw [this, smul_smul, inv_mul_cancel₀ hpos, one_smul]

end Transitive

theorem normAt_smul_base {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (g : Γ)
    (m : M) : normAt hx₀ M (g • x₀) m = normStab hx₀ M (M.ρ g⁻¹ m) := by
  unfold normStab normAt
  have hset : (transp_finite hx₀ (g • x₀)).toFinset =
      (transp_finite hx₀ x₀).toFinset.image (fun γ => γ * g⁻¹) := by
    ext γ
    simp only [Set.Finite.mem_toFinset, Finset.mem_image, transp_smul, Set.mem_image]
  rw [hset, LinearMap.sum_apply, LinearMap.sum_apply,
    Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [map_mul, Module.End.mul_apply]

/-- If `g` normalizes the stabilizer of the base point, the stabilizer sum commutes with `g`. -/
theorem normStab_conj {x₀ : X} (hx₀ : Finite (MulAction.stabilizer Γ x₀)) (M : Rep ℚ Γ) (g : Γ)
    (hg : ∀ γ : Γ, γ ∈ MulAction.stabilizer Γ x₀ ↔ g⁻¹ * γ * g ∈ MulAction.stabilizer Γ x₀)
    (m : M) : normStab hx₀ M (M.ρ g m) = M.ρ g (normStab hx₀ M m) := by
  unfold normStab normAt
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  have hmem : ∀ γ : Γ, γ ∈ (transp_finite hx₀ x₀).toFinset ↔ γ ∈ MulAction.stabilizer Γ x₀ := by
    intro γ
    rw [Set.Finite.mem_toFinset, transp_base]
    rfl
  refine Finset.sum_nbij' (fun γ => g⁻¹ * γ * g) (fun γ => g * γ * g⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [hmem] at hγ ⊢
    exact (hg γ).mp hγ
  · intro γ hγ
    rw [hmem] at hγ ⊢
    exact (hg _).mpr (by simpa [mul_assoc] using hγ)
  · intro γ _; simp [mul_assoc]
  · intro γ _; simp [mul_assoc]
  · intro γ _
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    simp [mul_assoc]

end TernaryPeriodPolynomials.Argument.BinaryDuality
