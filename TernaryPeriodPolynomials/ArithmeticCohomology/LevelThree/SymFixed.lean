module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularSymDimension

@[expose] public section


/-!
# Fixed vectors of the level-three generators on `Sym^m(ℂ²)`

For the shears `T = [[1,c],[0,1]]`, `L = [[1,0],[c,1]]` (`c ≠ 0`) acting on homogeneous binary
polynomials of degree `m` by `p ↦ det^e · p(g⁻¹ x)`:

* `finrank_fixed_upper`, `finrank_fixed_lower`: both fixed spaces are lines (`X₁^m`, resp. `X₀^m`);
* `fixed_upper_inf_fixed_lower`: for `m > 0` no nonzero vector is fixed by both;
* `moved_upper_sup_moved_lower`: for `m > 0`, `(T - 1)V + (L - 1)V = V` (no coinvariants);
* `finrank_fixed_elliptic`: the order-three element `E = [[-2,1],[-3,1]] = T L⁻¹` (for `T = [[1,1],[0,1]]`,
  `L = [[1,0],[3,1]]`) has `dim V^E = #{a ≤ m : 3 ∣ m + a}`.

The arguments are by evaluation: a polynomial invariant under a shear is constant along the
corresponding lines, and a homogeneous polynomial is determined by one value on each line through
the origin.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.SymFixed

open MvPolynomial Matrix GeneralEisenstein Module
open TernaryPeriodPolynomials.Spectral.ModularSymDimension
  (eval_substitute polynomial_eval_aeval monomialBasis finrank_fixed_of_conj diagGL)

section Evaluation

/-- A homogeneous polynomial of degree `m` scales by `c^m`. -/
theorem eval_smul_of_homogeneous {m : ℕ} {p : Binary.Poly} (hp : p.IsHomogeneous m) (c : ℂ)
    (x : Fin 2 → ℂ) : eval (c • x) p = c ^ m * eval x p := by
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg := hp (mem_support_iff.mp hd)
  simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one] at hdeg
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- A polynomial that is `1`-periodic along an affine line is constant on it. -/
theorem eval_line_const (p : Binary.Poly) (u w : Fin 2 → ℂ)
    (periodic : ∀ t : ℂ, eval (u + (t + 1) • w) p = eval (u + t • w) p) (t : ℂ) :
    eval (u + t • w) p = eval u p := by
  let r : Polynomial ℂ :=
    aeval (fun i => Polynomial.C (u i) + Polynomial.C (w i) * Polynomial.X) p
  have hr : ∀ s : ℂ, r.eval s = eval (u + s • w) p := by
    intro s
    rw [polynomial_eval_aeval]
    congr 2
    funext i
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have periodic_nat : ∀ k : ℕ, r.eval (k : ℂ) = r.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [← ih, hr, hr, Nat.cast_succ, periodic]
  have constant : r - Polynomial.C (r.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ)) Nat.cast_injective
    intro k
    simp [Polynomial.IsRoot, periodic_nat k]
  have value := congrArg (Polynomial.eval t) constant
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_zero, sub_eq_zero, hr, hr, zero_smul,
    add_zero] at value
  exact value

/-- A polynomial vanishing wherever the `i`-th coordinate is nonzero is zero. -/
theorem eq_zero_of_eval_eq_zero (p : Binary.Poly) (i : Fin 2)
    (vanish : ∀ x : Fin 2 → ℂ, x i ≠ 0 → eval x p = 0) : p = 0 := by
  have product : X i * p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x i = 0
    · rw [hx, zero_mul]
    · rw [vanish x hx, mul_zero]
  exact (mul_eq_zero.mp product).resolve_left (X_ne_zero i)

theorem eval_vec (p : Binary.Poly) (x : Fin 2 → ℂ) : eval x p = eval ![x 0, x 1] p := by
  congr 2
  funext i
  fin_cases i <;> rfl

/-- The action of a determinant-one matrix, evaluated. -/
theorem eval_action_of_det (e : ℤ) (g : Binary.GL2) (hdet : (GeneralLinearGroup.det g : ℂ) = 1)
    (p : Binary.Poly) (x : Fin 2 → ℂ) :
    eval x (Binary.action e g p) =
      eval (fun i => ∑ j, ((g⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) i j * x j) p := by
  rw [Binary.action_apply]
  have hchar : Binary.determinantCharacter e g = 1 := by
    change ((GeneralLinearGroup.det g : ℂˣ) : ℂ) ^ e = 1
    rw [hdet, _root_.one_zpow]
  rw [hchar, one_smul, eval_substitute]

end Evaluation

section Shears

instance (m : ℕ) : FiniteDimensional ℂ (Binary.HomogeneousPoly m) :=
  Module.Finite.of_basis (monomialBasis m)

/-- `[[1, c], [0, 1]]`. -/
def upperC (c : ℂ) : Binary.GL2 :=
  ⟨!![1, c; 0, 1], !![1, -c; 0, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- `[[1, 0], [c, 1]]`. -/
def lowerC (c : ℂ) : Binary.GL2 :=
  ⟨!![1, 0; c, 1], !![1, 0; -c, 1], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem upperC_det (c : ℂ) : (GeneralLinearGroup.det (upperC c) : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det !![1, c; 0, 1] = 1
  simp [Matrix.det_fin_two_of]

theorem lowerC_det (c : ℂ) : (GeneralLinearGroup.det (lowerC c) : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det !![1, 0; c, 1] = 1
  simp [Matrix.det_fin_two_of]

theorem eval_upper (e : ℤ) (c : ℂ) (p : Binary.Poly) (a b : ℂ) :
    eval ![a, b] (Binary.action e (upperC c) p) = eval ![a - c * b, b] p := by
  rw [eval_action_of_det e _ (upperC_det c)]
  congr 2
  funext i
  fin_cases i <;> first
    | (simp [upperC, Fin.sum_univ_two]; ring)
    | simp [upperC, Fin.sum_univ_two]

theorem eval_lower (e : ℤ) (c : ℂ) (p : Binary.Poly) (a b : ℂ) :
    eval ![a, b] (Binary.action e (lowerC c) p) = eval ![a, b - c * a] p := by
  rw [eval_action_of_det e _ (lowerC_det c)]
  congr 2
  funext i
  fin_cases i <;> first
    | (simp [lowerC, Fin.sum_univ_two]; ring)
    | simp [lowerC, Fin.sum_univ_two]

variable {m : ℕ} (e : ℤ)

/-- The fixed space of `g` on `Sym^m ⊗ det^e`. -/
abbrev fixedSpace (g : Binary.GL2) : Submodule ℂ (Binary.HomogeneousPoly m) :=
  LinearMap.ker (Binary.homogeneousAction m e g - 1)

/-- The image of `g - 1` on `Sym^m ⊗ det^e`. -/
abbrev movedSpace (g : Binary.GL2) : Submodule ℂ (Binary.HomogeneousPoly m) :=
  LinearMap.range (Binary.homogeneousAction m e g - 1)

theorem mem_fixedSpace {g : Binary.GL2} {v : Binary.HomogeneousPoly m} :
    v ∈ fixedSpace e g ↔ Binary.homogeneousAction m e g v = v := by
  simp [sub_eq_zero]

theorem isHomogeneous (v : Binary.HomogeneousPoly m) : v.val.IsHomogeneous m :=
  (mem_homogeneousSubmodule _ _).mp v.property

/-- Values of a `T`-fixed vector: `v(a, b) = b^m v(0, 1)` for `b ≠ 0`. -/
theorem eval_of_upper_fixed {c : ℂ} (hc : c ≠ 0) {v : Binary.HomogeneousPoly m}
    (fixed : v ∈ fixedSpace e (upperC c)) (a b : ℂ) (hb : b ≠ 0) :
    eval ![a, b] v.val = b ^ m * eval ![0, 1] v.val := by
  have invariant : ∀ a b : ℂ, eval ![a - c * b, b] v.val = eval ![a, b] v.val := by
    intro a b
    have h := congrArg (fun w : Binary.HomogeneousPoly m => eval ![a, b] w.val)
      ((mem_fixedSpace e).mp fixed)
    simp only [Binary.homogeneousAction_coe, eval_upper] at h
    exact h
  have line := eval_line_const v.val ![a, b] ![-(c * b), 0] (by
    intro t
    have h := invariant (a + t * -(c * b)) b
    rw [eval_vec _ (![a, b] + (t + 1) • ![-(c * b), 0]),
      eval_vec _ (![a, b] + t • ![-(c * b), 0])]
    convert h using 3 <;> funext i <;> fin_cases i <;> first | (simp; ring) | simp) (a / (c * b))
  have point : ![a, b] + (a / (c * b)) • ![-(c * b), 0] = b • ![(0 : ℂ), 1] := by
    funext i
    fin_cases i
    · simp [div_mul_cancel₀ a (mul_ne_zero hc hb)]
    · simp
  rw [point, eval_smul_of_homogeneous (isHomogeneous v)] at line
  exact line.symm

/-- Values of an `L`-fixed vector: `v(a, b) = a^m v(1, 0)` for `a ≠ 0`. -/
theorem eval_of_lower_fixed {c : ℂ} (hc : c ≠ 0) {v : Binary.HomogeneousPoly m}
    (fixed : v ∈ fixedSpace e (lowerC c)) (a b : ℂ) (ha : a ≠ 0) :
    eval ![a, b] v.val = a ^ m * eval ![1, 0] v.val := by
  have invariant : ∀ a b : ℂ, eval ![a, b - c * a] v.val = eval ![a, b] v.val := by
    intro a b
    have h := congrArg (fun w : Binary.HomogeneousPoly m => eval ![a, b] w.val)
      ((mem_fixedSpace e).mp fixed)
    simp only [Binary.homogeneousAction_coe, eval_lower] at h
    exact h
  have line := eval_line_const v.val ![a, b] ![0, -(c * a)] (by
    intro t
    have h := invariant a (b + t * -(c * a))
    rw [eval_vec _ (![a, b] + (t + 1) • ![0, -(c * a)]),
      eval_vec _ (![a, b] + t • ![0, -(c * a)])]
    convert h using 3 <;> funext i <;> fin_cases i <;> first | (simp; ring) | simp) (b / (c * a))
  have point : ![a, b] + (b / (c * a)) • ![0, -(c * a)] = a • ![(1 : ℂ), 0] := by
    funext i
    fin_cases i
    · simp
    · simp [div_mul_cancel₀ b (mul_ne_zero hc ha)]
  rw [point, eval_smul_of_homogeneous (isHomogeneous v)] at line
  exact line.symm

/-- The monomial `X_i^m` as a vector of `Sym^m`. -/
def powerVector (i : Fin 2) (m : ℕ) : Binary.HomogeneousPoly m :=
  ⟨X i ^ m, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i m)⟩

theorem powerVector_ne_zero (i : Fin 2) (m : ℕ) : powerVector i m ≠ 0 := by
  intro h
  have h' := congrArg Subtype.val h
  exact pow_ne_zero m (X_ne_zero i) h'

theorem powerVector_one_mem_upper (c : ℂ) : powerVector 1 m ∈ fixedSpace e (upperC c) := by
  rw [mem_fixedSpace]
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [Binary.homogeneousAction_coe, eval_vec, eval_upper, eval_vec _ x]
  simp [powerVector]

theorem powerVector_zero_mem_lower (c : ℂ) : powerVector 0 m ∈ fixedSpace e (lowerC c) := by
  rw [mem_fixedSpace]
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [Binary.homogeneousAction_coe, eval_vec, eval_lower, eval_vec _ x]
  simp [powerVector]

/-- Evaluation at a point, as a linear functional on `Sym^m`. -/
def evalAt (x : Fin 2 → ℂ) : Binary.HomogeneousPoly m →ₗ[ℂ] ℂ where
  toFun v := eval x v.val
  map_add' v w := by simp
  map_smul' c v := by simp

theorem finrank_le_one_of_injOn (S : Submodule ℂ (Binary.HomogeneousPoly m)) (x : Fin 2 → ℂ)
    (injective : ∀ v ∈ S, eval x (v : Binary.HomogeneousPoly m).val = 0 → v = 0) :
    finrank ℂ S ≤ 1 := by
  have h : Function.Injective ((evalAt (m := m) x).comp S.subtype) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    exact Subtype.ext (injective v.val v.property hv)
  have := LinearMap.finrank_le_finrank_of_injective h
  rwa [Module.finrank_self] at this

theorem one_le_finrank_of_mem (S : Submodule ℂ (Binary.HomogeneousPoly m)) (v : Binary.HomogeneousPoly m)
    (hv : v ∈ S) (nonzero : v ≠ 0) : 1 ≤ finrank ℂ S := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rw [Submodule.finrank_eq_zero] at h
  rw [h, Submodule.mem_bot] at hv
  exact nonzero hv

/-- **`dim V^T = 1`** for a nontrivial upper shear. -/
theorem finrank_fixed_upper {c : ℂ} (hc : c ≠ 0) :
    finrank ℂ (fixedSpace (m := m) e (upperC c)) = 1 := by
  apply le_antisymm
  · apply finrank_le_one_of_injOn _ ![0, 1]
    intro v hv zero
    apply Subtype.ext
    apply eq_zero_of_eval_eq_zero _ 1
    intro x hx
    rw [eval_vec, eval_of_upper_fixed e hc hv _ _ hx, zero, mul_zero]
  · exact one_le_finrank_of_mem _ _ (powerVector_one_mem_upper e c) (powerVector_ne_zero 1 m)

/-- **`dim V^L = 1`** for a nontrivial lower shear. -/
theorem finrank_fixed_lower {c : ℂ} (hc : c ≠ 0) :
    finrank ℂ (fixedSpace (m := m) e (lowerC c)) = 1 := by
  apply le_antisymm
  · apply finrank_le_one_of_injOn _ ![1, 0]
    intro v hv zero
    apply Subtype.ext
    apply eq_zero_of_eval_eq_zero _ 0
    intro x hx
    rw [eval_vec, eval_of_lower_fixed e hc hv _ _ hx, zero, mul_zero]
  · exact one_le_finrank_of_mem _ _ (powerVector_zero_mem_lower e c) (powerVector_ne_zero 0 m)

/-- **No invariants**: for `m > 0`, no nonzero vector is fixed by both shears. -/
theorem fixed_upper_inf_fixed_lower (positive : 0 < m) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    fixedSpace (m := m) e (upperC c) ⊓ fixedSpace e (lowerC c') = ⊥ := by
  rw [eq_bot_iff]
  rintro v ⟨hT, hL⟩
  have upper := eval_of_upper_fixed e hc hT
  have lower := eval_of_lower_fixed e hc' hL
  have equal : eval ![0, 1] v.val = eval ![1, 0] v.val := by
    have h1 := upper 1 1 one_ne_zero
    have h2 := lower 1 1 one_ne_zero
    rw [one_pow, one_mul] at h1 h2
    rw [← h1, h2]
  have zero : eval ![0, 1] v.val = 0 := by
    have h1 := upper 1 2 two_ne_zero
    have h2 := lower 1 2 one_ne_zero
    rw [h1, one_pow, one_mul, ← equal] at h2
    have h3 : ((2 : ℂ) ^ m - 1) * eval ![0, 1] v.val = 0 := by rw [sub_mul, h2, one_mul, sub_self]
    have h4 : (2 : ℂ) ^ m - 1 ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have h' : ((2 ^ m : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by push_cast; exact h
      have h'' := Nat.cast_injective h'
      have : 1 < 2 ^ m := Nat.one_lt_two_pow (by omega)
      omega
    exact (mul_eq_zero.mp h3).resolve_left h4
  rw [Submodule.mem_bot]
  apply Subtype.ext
  apply eq_zero_of_eval_eq_zero _ 1
  intro x hx
  rw [eval_vec, upper _ _ hx, zero, mul_zero]

/-- `dim Sym^m = m + 1`. -/
theorem finrank_sym (m : ℕ) : finrank ℂ (Binary.HomogeneousPoly m) = m + 1 := by
  rw [Module.finrank_eq_card_basis (monomialBasis m), Fintype.card_fin]

theorem eval_upper_moved (c : ℂ) (w : Binary.HomogeneousPoly m) (hw : w ∈ movedSpace e (upperC c)) :
    eval ![1, 0] w.val = 0 := by
  obtain ⟨v, rfl⟩ := hw
  change eval ![1, 0] ((Binary.homogeneousAction m e (upperC c) v).val - v.val) = 0
  rw [map_sub, Binary.homogeneousAction_coe, eval_upper]
  simp

/-- The vector `X₀^{m-1} X₁`. -/
def mixedVector (m : ℕ) : Binary.HomogeneousPoly (m + 1) :=
  ⟨X 0 ^ m * X 1, (mem_homogeneousSubmodule _ _).mpr
    ((isHomogeneous_X_pow 0 m).mul (isHomogeneous_X ℂ 1))⟩

/-- **No coinvariants**: for `m > 0` and `c' ≠ 0`, `(T - 1)V + (L - 1)V = V`. -/
theorem moved_upper_sup_moved_lower (positive : 0 < m) {c c' : ℂ} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    movedSpace (m := m) e (upperC c) ⊔ movedSpace e (lowerC c') = ⊤ := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have rank_nullity := LinearMap.finrank_range_add_finrank_ker
    (Binary.homogeneousAction (k + 1) e (upperC c) - 1)
  rw [finrank_sym] at rank_nullity
  have fixedT := finrank_fixed_upper (m := k + 1) e hc
  change finrank ℂ (movedSpace e (upperC c)) + finrank ℂ (fixedSpace e (upperC c)) = _ at rank_nullity
  let w : Binary.HomogeneousPoly (k + 1) :=
    Binary.homogeneousAction (k + 1) e (lowerC c') (mixedVector k) - mixedVector k
  have hw : w ∈ movedSpace e (lowerC c') := ⟨mixedVector k, rfl⟩
  have value : eval ![1, 0] w.val = -c' := by
    change eval ![1, 0] ((Binary.homogeneousAction (k + 1) e (lowerC c') (mixedVector k)).val -
      (mixedVector k).val) = -c'
    rw [map_sub, Binary.homogeneousAction_coe, eval_lower]
    simp [mixedVector]
  have strict : movedSpace (m := k + 1) e (upperC c) < movedSpace e (upperC c) ⊔ movedSpace e (lowerC c') := by
    apply lt_of_le_of_ne le_sup_left
    intro h
    have member : w ∈ movedSpace e (upperC c) := h ▸ Submodule.mem_sup_right hw
    have zero := eval_upper_moved e c w member
    rw [value, neg_eq_zero] at zero
    exact hc' zero
  have bigger := Submodule.finrank_lt_finrank_of_lt strict
  apply Submodule.eq_top_of_finrank_eq
  have le := Submodule.finrank_le (movedSpace (m := k + 1) e (upperC c) ⊔ movedSpace e (lowerC c'))
  rw [finrank_sym] at le ⊢
  omega

end Shears

section Elliptic

/-- The primitive cube root of unity `exp(2πi/3)`. -/
abbrev zeta3 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (3 : ℕ))

theorem zeta3_primitive : IsPrimitiveRoot zeta3 3 := Complex.isPrimitiveRoot_exp 3 (by norm_num)

theorem zeta3_ne_zero : zeta3 ≠ 0 := Complex.exp_ne_zero _

theorem zeta3_relation : zeta3 ^ 2 + zeta3 + 1 = 0 := by
  have h := zeta3_primitive.geom_sum_eq_zero (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add] at h
  linear_combination h

theorem zeta3_inv : zeta3⁻¹ = zeta3 ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_succ']
  exact zeta3_primitive.pow_eq_one

/-- The elliptic element `E = [[-2, 1], [-3, 1]]` of order three. -/
def ellipticC : Binary.GL2 :=
  ⟨!![-2, 1; -3, 1], !![1, -1; 3, -2], by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]⟩

theorem upper_mul_lower_inv : upperC 1 * (lowerC 3)⁻¹ = ellipticC := by
  apply Units.ext
  change !![(1 : ℂ), 1; 0, 1] * !![1, 0; -3, 1] = !![-2, 1; -3, 1]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- The eigenvector matrix of `E`: columns `(1, 2 + ζ)` and `(1, 2 + ζ⁻¹)`. -/
def eigenE : Binary.GL2 :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; 2 + zeta3, 2 + zeta3⁻¹] (by
    rw [Matrix.det_fin_two_of, zeta3_inv]
    intro h
    have h' : zeta3 * (zeta3 - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact zeta3_ne_zero h0
    · have : zeta3 = 1 := sub_eq_zero.mp h1
      exact (zeta3_primitive.ne_one (by norm_num)) this)

theorem conj_E : ellipticC * eigenE = eigenE * diagGL zeta3 zeta3_ne_zero := by
  apply Units.ext
  change !![(-2 : ℂ), 1; -3, 1] * !![1, 1; 2 + zeta3, 2 + zeta3⁻¹] =
    !![1, 1; 2 + zeta3, 2 + zeta3⁻¹] * !![zeta3, 0; 0, zeta3⁻¹]
  have r := zeta3_relation
  rw [zeta3_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -r
  · linear_combination (-(1 - zeta3 + zeta3 ^ 2)) * r

theorem zeta3_inv_pow (m a : ℕ) (ha : a ≤ m) :
    zeta3 ^ (m - a) * zeta3⁻¹ ^ a = zeta3 ^ (m + a) := by
  rw [zeta3_inv, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- **`dim V^E = #{a ≤ m : 3 ∣ m + a}`**. -/
theorem finrank_fixed_elliptic (m : ℕ) (e : ℤ) :
    finrank ℂ (fixedSpace (m := m) e ellipticC) =
      (Finset.univ.filter (fun a : Fin (m + 1) => 3 ∣ m + a.val)).card := by
  rw [finrank_fixed_of_conj m e _ eigenE zeta3 zeta3_ne_zero conj_E]
  congr 1
  apply Finset.filter_congr
  intro a _
  rw [zeta3_inv_pow m a.val (Nat.lt_succ_iff.mp a.isLt), zeta3_primitive.pow_eq_one_iff_dvd]

end Elliptic

end TernaryPeriodPolynomials.LevelThree.SymFixed
