module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularH1
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Classical.BinaryCocycle
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Binary.EndpointFormAnalytic
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.MvPolynomial.Polynomial

@[expose] public section


/-!
# Fixed spaces of `S` and `U = ST` on `Sym^m(ℂ²)` and `dim H¹(SL₂(ℤ), Sym^m)`

`S` and `U` are diagonalizable over `ℂ` with eigenvalues `±i` and `ζ₆^{±1}`; on the monomials of
the conjugated eigenbasis they act by `i^{m+2a}` and `ζ₆^{m+4a}`.  Counting fixed monomials and
inserting the counts into the Mayer–Vietoris formula of `ModularH1` gives `dim H¹(SL₂(ℤ), Sym^m)`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Spectral.ModularSymDimension

open TernaryPeriodPolynomials.SphericalDetection.Helpers Matrix MvPolynomial
open TernaryPeriodPolynomials.Spectral.ModularH1
open GeneralEisenstein

section Eigen

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]

/-- For an eigenbasis, the fixed space is spanned by the basis vectors with eigenvalue one. -/
theorem finrank_fixed_of_eigenbasis (T : Module.End ℂ V) (b : Module.Basis ι ℂ V) (eigenvalue : ι → ℂ)
    (eigen : ∀ i, T (b i) = eigenvalue i • b i) :
    Module.finrank ℂ (LinearMap.ker (T - 1)) = (Finset.univ.filter (fun i => eigenvalue i = 1)).card := by
  classical
  let F := {i // eigenvalue i = 1}
  have hspan : LinearMap.ker (T - 1) = Submodule.span ℂ (Set.range (fun i : F => b i.val)) := by
    apply le_antisymm
    · intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hv
      have expand := b.sum_repr v
      have coefficient : ∀ i, eigenvalue i ≠ 1 → b.repr v i = 0 := by
        intro i hi
        have hT : T v = ∑ j, (b.repr v j * eigenvalue j) • b j := by
          conv_lhs => rw [← expand]
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [map_smul, eigen, smul_smul]
        have hrepr := congrArg (fun w => b.repr w i) (hT.symm.trans hv)
        simp only [Module.Basis.repr_sum_self] at hrepr
        have : b.repr v i * (eigenvalue i - 1) = 0 := by rw [mul_sub, mul_one, hrepr, sub_self]
        exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hi)
      rw [← expand]
      apply Submodule.sum_mem
      intro i _
      by_cases hi : eigenvalue i = 1
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · rw [coefficient i hi, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change b i.val ∈ LinearMap.ker (T - 1)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, eigen, i.property, one_smul,
        sub_self]
  have independent : LinearIndependent ℂ (fun i : F => b i.val) :=
    b.linearIndependent.comp (fun i : F => i.val) Subtype.val_injective
  rw [hspan, finrank_span_eq_card independent, Fintype.card_subtype]

end Eigen


section Diagonal

/-- The monomial basis `X₀^a X₁^{m-a}` of `Sym^m`. -/
def monomialBasis (m : ℕ) : Module.Basis (Fin (m + 1)) ℂ (Binary.HomogeneousPoly m) :=
  (binaryMonomialBasis m).reindex (binaryWeightIndex m)

theorem monomialBasis_coe (m : ℕ) (a : Fin (m + 1)) :
    (monomialBasis m a).val = X 0 ^ a.val * X 1 ^ (m - a.val) := by
  rw [monomialBasis, Module.Basis.reindex_apply]
  exact binaryMonomialBasis_weightExponent m a

/-- `diag(α, α⁻¹)`. -/
def diagGL (α : ℂ) (hα : α ≠ 0) : Binary.GL2 :=
  ⟨!![α, 0; 0, α⁻¹], !![α⁻¹, 0; 0, α], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [hα],
   by ext i j; fin_cases i <;> fin_cases j <;> simp [hα]⟩

theorem diagGL_det (α : ℂ) (hα : α ≠ 0) : (GeneralLinearGroup.det (diagGL α hα) : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply]
  change Matrix.det !![α, 0; 0, α⁻¹] = 1
  rw [Matrix.det_fin_two_of]
  field_simp
  ring

theorem diagGL_action (m : ℕ) (e : ℤ) (α : ℂ) (hα : α ≠ 0) (a : Fin (m + 1)) :
    Binary.homogeneousAction m e (diagGL α hα) (monomialBasis m a) =
      (α ^ (m - a.val) * α⁻¹ ^ a.val) • monomialBasis m a := by
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.action_apply, Submodule.coe_smul, monomialBasis_coe]
  have hdet : Binary.determinantCharacter e (diagGL α hα) = 1 := by
    change ((GeneralLinearGroup.det (diagGL α hα) : ℂˣ) : ℂ) ^ e = 1
    rw [diagGL_det, _root_.one_zpow]
  rw [hdet, one_smul, map_mul, map_pow, map_pow, Binary.substitute_X, Binary.substitute_X]
  have hinv : (((diagGL α hα)⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) = !![α⁻¹, 0; 0, α] := rfl
  rw [hinv]
  simp only [Binary.linearForm, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    map_zero, zero_mul, add_zero, zero_add]
  rw [MvPolynomial.smul_eq_C_mul, mul_pow, mul_pow, ← map_pow, ← map_pow]
  rw [show MvPolynomial.C (α ^ (m - a.val) * α⁻¹ ^ a.val) =
    MvPolynomial.C (α⁻¹ ^ a.val) * MvPolynomial.C (α ^ (m - a.val)) by rw [← map_mul, mul_comm]]
  ring

end Diagonal


section Conjugate

/-- A group element acting through a representation, as a linear equivalence. -/
def actionEquiv {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) : V ≃ₗ[ℂ] V :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

/-- If `g P = P diag(α, α⁻¹)`, the fixed space of `g` on `Sym^m` has dimension
`#{a ≤ m : α^{m-a} α^{-a} = 1}`. -/
theorem finrank_fixed_of_conj (m : ℕ) (e : ℤ) (g P : Binary.GL2) (α : ℂ) (hα : α ≠ 0)
    (conj : g * P = P * diagGL α hα) :
    Module.finrank ℂ (LinearMap.ker (Binary.homogeneousAction m e g - 1)) =
      (Finset.univ.filter (fun a : Fin (m + 1) => α ^ (m - a.val) * α⁻¹ ^ a.val = 1)).card := by
  let b := (monomialBasis m).map (actionEquiv (Binary.homogeneousAction m e) P)
  apply finrank_fixed_of_eigenbasis _ b
  intro a
  change Binary.homogeneousAction m e g (Binary.homogeneousAction m e P (monomialBasis m a)) =
    _ • Binary.homogeneousAction m e P (monomialBasis m a)
  rw [← Module.End.mul_apply, ← map_mul, conj, map_mul, Module.End.mul_apply, diagGL_action,
    map_smul]

end Conjugate


section Modular

/-- The image of an element of `SL₂(ℤ)` in `GL₂(ℂ)`. -/
abbrev toGLC (g : Modular) : Binary.GL2 :=
  GeneralLinearGroup.map (Int.castRingHom ℂ) (SpecialLinearGroup.toGL g)

theorem toGLC_val (g : Modular) : (toGLC g).val = (g.val).map (Int.castRingHom ℂ) := rfl

/-- `Sym^m(ℂ²) ⊗ det^twist` as a representation of `SL₂(ℤ)`. -/
abbrev symRep (m : ℕ) (twist : ℤ) : Rep.{0, 0, 0} ℂ Modular := modularBinaryRep m twist

theorem symRep_ρ (m : ℕ) (twist : ℤ) (g : Modular) :
    (symRep m twist).ρ g = Binary.homogeneousAction m twist (toGLC g) := rfl

/-- The eigenvector matrix of `S`. -/
def eigenS : Binary.GL2 :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; -Complex.I, Complex.I] (by
    rw [Matrix.det_fin_two_of]
    simp)

theorem conj_S : toGLC ModularGroup.S * eigenS = eigenS * diagGL Complex.I Complex.I_ne_zero := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, toGLC_val, ModularGroup.coe_S]
  change Matrix.map !![(0 : ℤ), -1; 1, 0] (Int.castRingHom ℂ) * !![1, 1; -Complex.I, Complex.I] =
    !![1, 1; -Complex.I, Complex.I] * !![Complex.I, 0; 0, Complex.I⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The primitive sixth root of unity `exp(2πi/6)`. -/
abbrev zeta6 : ℂ := Complex.exp (2 * Real.pi * Complex.I / (6 : ℕ))

theorem zeta6_primitive : IsPrimitiveRoot zeta6 6 := Complex.isPrimitiveRoot_exp 6 (by norm_num)

theorem zeta6_ne_zero : zeta6 ≠ 0 := Complex.exp_ne_zero _

theorem zeta6_relation : zeta6 ^ 2 - zeta6 + 1 = 0 := by
  have h6 : zeta6 ^ 6 = 1 := zeta6_primitive.pow_eq_one
  have h3 : zeta6 ^ 3 ≠ 1 := zeta6_primitive.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have h2 : zeta6 ^ 2 ≠ 1 := zeta6_primitive.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
  have cube : zeta6 ^ 3 = -1 := by
    have : (zeta6 ^ 3 - 1) * (zeta6 ^ 3 + 1) = 0 := by ring_nf; rw [h6]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h3
    · exact eq_neg_of_add_eq_zero_left h
  have factor : (zeta6 + 1) * (zeta6 ^ 2 - zeta6 + 1) = 0 := by
    linear_combination cube
  rcases mul_eq_zero.mp factor with h | h
  · exfalso
    apply h2
    rw [eq_neg_of_add_eq_zero_left h]
    norm_num
  · exact h

/-- The eigenvector matrix of `U = ST`. -/
def eigenU : Binary.GL2 :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 1; -zeta6, -zeta6⁻¹] (by
    rw [Matrix.det_fin_two_of]
    intro h
    have h' : zeta6 * zeta6 = 1 := by
      field_simp [zeta6_ne_zero] at h
      linear_combination h
    have h2 : zeta6 ^ 2 ≠ 1 := zeta6_primitive.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num)
    exact h2 (by rw [pow_two]; exact h'))

theorem conj_U : toGLC modularOrderSix * eigenU = eigenU * diagGL zeta6 zeta6_ne_zero := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, toGLC_val, modularOrderSix_matrix]
  change Matrix.map !![(0 : ℤ), -1; 1, 1] (Int.castRingHom ℂ) * !![1, 1; -zeta6, -zeta6⁻¹] =
    !![1, 1; -zeta6, -zeta6⁻¹] * !![zeta6, 0; 0, zeta6⁻¹]
  have r := zeta6_relation
  have hz := zeta6_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination r
  · field_simp
    linear_combination r

theorem modularS_square : ModularGroup.S ^ 2 = (-1 : SpecialLinearGroup (Fin 2) ℤ) := by decide

theorem conj_central : toGLC (ModularGroup.S ^ 2) * 1 = 1 * diagGL (-1) (by norm_num) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, toGLC_val, modularS_square]
  change Matrix.map ((-1 : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)
    (Int.castRingHom ℂ) * 1 = 1 * !![-1, 0; 0, (-1)⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem I_inv_pow (m a : ℕ) (ha : a ≤ m) :
    Complex.I ^ (m - a) * Complex.I⁻¹ ^ a = Complex.I ^ (m + 2 * a) := by
  have hinv : Complex.I⁻¹ = Complex.I ^ 3 := by
    rw [Complex.inv_I]
    simp [pow_succ]
  rw [hinv, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem zeta6_inv_pow (m a : ℕ) (ha : a ≤ m) :
    zeta6 ^ (m - a) * zeta6⁻¹ ^ a = zeta6 ^ (m + 4 * a) := by
  have hinv : zeta6⁻¹ = zeta6 ^ 5 := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ']
    exact zeta6_primitive.pow_eq_one
  rw [hinv, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- `dim W^S = #{a ≤ m : 4 ∣ m + 2a}`. -/
theorem finrank_fixed_S (m : ℕ) (twist : ℤ) :
    Module.finrank ℂ (fixedSpace (symRep m twist) ModularGroup.S) =
      (Finset.univ.filter (fun a : Fin (m + 1) => 4 ∣ m + 2 * a.val)).card := by
  show Module.finrank ℂ (LinearMap.ker (Binary.homogeneousAction m twist (toGLC ModularGroup.S) -
    (1 : Module.End ℂ (Binary.HomogeneousPoly m)))) = _
  rw [finrank_fixed_of_conj m twist _ eigenS Complex.I Complex.I_ne_zero conj_S]
  congr 1
  apply Finset.filter_congr
  intro a _
  rw [I_inv_pow m a.val (Nat.lt_succ_iff.mp a.isLt), Complex.isPrimitiveRoot_I.pow_eq_one_iff_dvd]

/-- `dim W^U = #{a ≤ m : 6 ∣ m + 4a}`. -/
theorem finrank_fixed_U (m : ℕ) (twist : ℤ) :
    Module.finrank ℂ (fixedSpace (symRep m twist) modularOrderSix) =
      (Finset.univ.filter (fun a : Fin (m + 1) => 6 ∣ m + 4 * a.val)).card := by
  show Module.finrank ℂ (LinearMap.ker (Binary.homogeneousAction m twist (toGLC modularOrderSix) -
    (1 : Module.End ℂ (Binary.HomogeneousPoly m)))) = _
  rw [finrank_fixed_of_conj m twist _ eigenU zeta6 zeta6_ne_zero conj_U]
  congr 1
  apply Finset.filter_congr
  intro a _
  rw [zeta6_inv_pow m a.val (Nat.lt_succ_iff.mp a.isLt), zeta6_primitive.pow_eq_one_iff_dvd]

/-- `S² = -1` acts by `(-1)^m`. -/
theorem finrank_centralFixed (m : ℕ) (twist : ℤ) :
    Module.finrank ℂ (centralFixed (symRep m twist)) = if Even m then m + 1 else 0 := by
  show Module.finrank ℂ
    (LinearMap.ker (Binary.homogeneousAction m twist (toGLC (ModularGroup.S ^ 2)) -
    (1 : Module.End ℂ (Binary.HomogeneousPoly m)))) = _
  rw [finrank_fixed_of_conj m twist _ 1 (-1) (by norm_num) conj_central]
  have hval : ∀ a : Fin (m + 1), (-1 : ℂ) ^ (m - a.val) * (-1 : ℂ)⁻¹ ^ a.val = (-1) ^ m := by
    intro a
    rw [inv_neg, inv_one, ← pow_add, Nat.sub_add_cancel (Nat.lt_succ_iff.mp a.isLt)]
  simp only [hval]
  by_cases h : Even m
  · rw [ite_eq_left h, h.neg_one_pow]
    simp
  · rw [ite_eq_right h, (Nat.not_even_iff_odd.mp h).neg_one_pow]
    have : (-1 : ℂ) ≠ 1 := by norm_num
    simp [this]

end Modular


section Invariants

theorem eval_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) (x : Fin 2 → ℂ) (p : Binary.Poly) :
    eval x (Binary.substitute M p) = eval (fun i => ∑ j, M i j * x j) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [Binary.substitute]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, Binary.substitute_X, map_mul, eval_X]
    simp [Binary.linearForm]

theorem polynomial_eval_aeval (f : Fin 2 → Polynomial ℂ) (t : ℂ) (p : Binary.Poly) :
    (aeval f p).eval t = eval (fun i => (f i).eval t) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp => rw [map_mul, map_mul, Polynomial.eval_mul, hp, aeval_X, eval_X]

/-- A polynomial invariant under `(a, b) ↦ (a - b, b)` is constant along horizontal lines. -/
theorem eval_eq_of_translation (p : Binary.Poly)
    (translation : ∀ a b : ℂ, eval ![a - b, b] p = eval ![a, b] p) (a b : ℂ) (hb : b ≠ 0) :
    eval ![a, b] p = eval ![0, b] p := by
  let r : Polynomial ℂ :=
    aeval ![Polynomial.C a - Polynomial.C b * Polynomial.X, Polynomial.C b] p
  have hr : ∀ t : ℂ, r.eval t = eval ![a - b * t, b] p := by
    intro t
    rw [polynomial_eval_aeval]
    have point : (fun i => (![Polynomial.C a - Polynomial.C b * Polynomial.X, Polynomial.C b] i).eval t) =
        ![a - b * t, b] := by
      funext i
      fin_cases i <;> simp
    rw [point]
  have periodic : ∀ k : ℕ, r.eval (k : ℂ) = r.eval 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih, hr, hr, Nat.cast_succ, ← translation (a - b * k) b]
      have shift : a - b * ((k : ℂ) + 1) = a - b * k - b := by ring
      rw [shift]
  have constant : r - Polynomial.C (r.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ)) Nat.cast_injective
    intro k
    simp [Polynomial.IsRoot, periodic k]
  have value := congrArg (Polynomial.eval (a / b)) constant
  rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_zero, sub_eq_zero, hr, hr] at value
  rw [mul_div_cancel₀ a hb, sub_self, mul_zero, sub_zero] at value
  exact value.symm

/-- A homogeneous polynomial of positive degree invariant under `T` and `S` vanishes. -/
theorem eq_zero_of_invariant {m : ℕ} (positive : 0 < m) (p : Binary.Poly) (homogeneous : p.IsHomogeneous m)
    (translation : ∀ a b : ℂ, eval ![a - b, b] p = eval ![a, b] p)
    (rotation : ∀ a b : ℂ, eval ![b, -a] p = eval ![a, b] p) : p = 0 := by
  let c := eval ![0, 1] p
  have vertical : ∀ b : ℂ, b ≠ 0 → eval ![0, b] p = c := by
    intro b hb
    have h1 := eval_eq_of_translation p translation (-1) b hb
    have h2 := rotation (-1) b
    have h3 := eval_eq_of_translation p translation b 1 one_ne_zero
    rw [neg_neg] at h2
    rw [← h1, ← h2, h3]
  have everywhere : ∀ x : Fin 2 → ℂ, x 0 ≠ 0 → eval x p = c := by
    intro x hx
    have hx' : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
    rw [hx', ← rotation, eval_eq_of_translation p translation _ _ (neg_ne_zero.mpr hx),
      vertical _ (neg_ne_zero.mpr hx)]
  have product : X 0 * (p - C c) = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_sub, eval_X, eval_C, map_zero]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · rw [everywhere x hx, sub_self, mul_zero]
  have hpc : p = C c := sub_eq_zero.mp ((mul_eq_zero.mp product).resolve_left (X_ne_zero 0))
  have hc : c = 0 := by
    have h := homogeneous.coeff_eq_zero (d := 0) (by simp; omega)
    rw [hpc, coeff_C, ite_eq_left rfl] at h
    exact h
  rw [hpc, hc, map_zero]

theorem toGLC_det (g : Modular) : (GeneralLinearGroup.det (toGLC g) : ℂ) = 1 := by
  rw [GeneralLinearGroup.val_det_apply, toGLC_val]
  have h := RingHom.map_det (Int.castRingHom ℂ) (g : Matrix (Fin 2) (Fin 2) ℤ)
  rw [g.property, map_one] at h
  exact h.symm

theorem modularS_inv_val :
    ((ModularGroup.S⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, 1; -1, 0] := by
  decide

/-- An `SL₂(ℤ)`-fixed vector is fixed by the inverse substitution. -/
theorem eval_of_fixed (m : ℕ) (twist : ℤ) (g : Modular) (v : Binary.HomogeneousPoly m)
    (fixed : Binary.homogeneousAction m twist (toGLC g) v = v) (x : Fin 2 → ℂ) :
    eval (fun i => ∑ j, ((toGLC g⁻¹ : Binary.GL2) : Matrix (Fin 2) (Fin 2) ℂ) i j * x j) v.val =
      eval x v.val := by
  have h := congrArg Subtype.val fixed
  rw [Binary.homogeneousAction_coe, Binary.action_apply] at h
  have hdet : Binary.determinantCharacter twist (toGLC g) = 1 := by
    change ((GeneralLinearGroup.det (toGLC g) : ℂˣ) : ℂ) ^ twist = 1
    rw [toGLC_det, _root_.one_zpow]
  rw [hdet, one_smul] at h
  have hinv : toGLC g⁻¹ = (toGLC g)⁻¹ := by simp [toGLC, map_inv]
  rw [← eval_substitute, hinv, h]

/-- `Sym^m(ℂ²)` has no nonzero `SL₂(ℤ)`-invariants for `m > 0`. -/
theorem inf_fixed_eq_bot {m : ℕ} (positive : 0 < m) (twist : ℤ) :
    fixedSpace (symRep m twist) ModularGroup.S ⊓ fixedSpace (symRep m twist) modularOrderSix = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have all := (mem_inf_fixed_iff (symRep m twist) v).mp hv
  have hT := eval_of_fixed m twist ModularGroup.T v (all ModularGroup.T)
  have hS := eval_of_fixed m twist ModularGroup.S v (all ModularGroup.S)
  have zero : (v : Binary.HomogeneousPoly m).val = 0 := by
    apply eq_zero_of_invariant positive _ v.property
    · intro a b
      have point : (fun i => ∑ j, ((toGLC ModularGroup.T⁻¹ : Binary.GL2) :
          Matrix (Fin 2) (Fin 2) ℂ) i j * ![a, b] j) = ![a - b, b] := by
        funext i
        rw [toGLC_val, ModularGroup.coe_T_inv]
        fin_cases i <;> simp [Fin.sum_univ_two, sub_eq_add_neg]
      rw [← hT ![a, b], point]
    · intro a b
      have point : (fun i => ∑ j, ((toGLC ModularGroup.S⁻¹ : Binary.GL2) :
          Matrix (Fin 2) (Fin 2) ℂ) i j * ![a, b] j) = ![b, -a] := by
        funext i
        rw [toGLC_val, modularS_inv_val]
        fin_cases i <;> simp [Fin.sum_univ_two]
      rw [← hS ![a, b], point]
  rw [Submodule.mem_bot]
  exact Subtype.ext zero

end Invariants


section Count

theorem card_filter_fin (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun a : Fin n => P a.val)).card = ((Finset.range n).filter P).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext a
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
    Finset.mem_range]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.isLt, hb⟩
  · rintro ⟨ha, hP⟩
    exact ⟨⟨a, ha⟩, hP, rfl⟩

/-- `#{a ≤ 2r : 4 ∣ 2r + 2a} = 2⌊r/2⌋ + 1`. -/
theorem count_S (r : ℕ) :
    ((Finset.range (2 * r + 1)).filter (fun a => 4 ∣ 2 * r + 2 * a)).card = 2 * (r / 2) + 1 := by
  have himage : (Finset.range (2 * (r / 2) + 1)).image (fun j => r % 2 + 2 * j) =
      (Finset.range (2 * r + 1)).filter (fun a => 4 ∣ 2 * r + 2 * a) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor
      · omega
      · rw [Nat.dvd_iff_mod_eq_zero]; omega
    · rintro ⟨ha, hdvd⟩
      rw [Nat.dvd_iff_mod_eq_zero] at hdvd
      exact ⟨a / 2, by omega, by omega⟩
  rw [← himage, Finset.card_image_of_injective _ (by
    intro x y h
    have h' : r % 2 + 2 * x = r % 2 + 2 * y := h
    omega), Finset.card_range]

/-- `#{a ≤ 2r : 6 ∣ 2r + 4a} = 2⌊r/3⌋ + 1`. -/
theorem count_U (r : ℕ) :
    ((Finset.range (2 * r + 1)).filter (fun a => 6 ∣ 2 * r + 4 * a)).card = 2 * (r / 3) + 1 := by
  have himage : (Finset.range (2 * (r / 3) + 1)).image (fun j => r % 3 + 3 * j) =
      (Finset.range (2 * r + 1)).filter (fun a => 6 ∣ 2 * r + 4 * a) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      constructor
      · omega
      · rw [Nat.dvd_iff_mod_eq_zero]; omega
    · rintro ⟨ha, hdvd⟩
      obtain ⟨c, hc⟩ := hdvd
      have hmod : a % 3 = r % 3 := by omega
      have hr := Nat.div_add_mod r 3
      have ha3 := Nat.div_add_mod a 3
      refine ⟨a / 3, ?_, ?_⟩ <;> omega
  rw [← himage, Finset.card_image_of_injective _ (by
    intro x y h
    have h' : r % 3 + 3 * x = r % 3 + 3 * y := h
    omega), Finset.card_range]

end Count

section Formula

/-- **`dim H¹(SL₂(ℤ), Sym^{2r}(ℂ²) ⊗ det^twist) = 2(r - ⌊r/2⌋ - ⌊r/3⌋) - 1`** for `r ≥ 1`
(stated additively). -/
theorem finrank_H1_sym (r : ℕ) (positive : 0 < r) (twist : ℤ) :
    Module.finrank ℂ (groupCohomology.H1 (symRep (2 * r) twist)) + (2 * (r / 2) + 1) +
      (2 * (r / 3) + 1) = 2 * r + 1 := by
  have : FiniteDimensional ℂ (symRep (2 * r) twist) :=
    Module.Finite.of_basis (monomialBasis (2 * r))
  have h := finrank_H1_add (symRep (2 * r) twist)
  rw [finrank_fixed_S, finrank_fixed_U, finrank_centralFixed, ite_eq_left (even_two_mul r),
    inf_fixed_eq_bot (by omega), finrank_bot] at h
  rw [card_filter_fin (2 * r + 1) (fun a => 4 ∣ 2 * r + 2 * a),
    card_filter_fin (2 * r + 1) (fun a => 6 ∣ 2 * r + 4 * a), count_S, count_U] at h
  omega

/-- From Mathlib's level-one dimension formula:
`dim S_{2r+2}(SL₂(ℤ)) = r - ⌊r/2⌋ - ⌊r/3⌋ - 1` for `r ≥ 1`. -/
theorem finrank_cuspForm_levelOne (r : ℕ) (positive : 0 < r) :
    Module.finrank ℂ (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
      ((2 * r + 2 : ℕ) : ℤ)) = r - r / 2 - r / 3 - 1 := by
  have hk : Even (2 * r + 2) := ⟨r + 1, by ring⟩
  have h1 := ModularForm.dimension_level_one (2 * r + 2) hk
  have h2 := ModularForm.rank_eq_one_add_rank_cuspForm (k := 2 * r + 2) (by omega) hk
  rw [h1] at h2
  have hlt : Module.rank ℂ (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
      ((2 * r + 2 : ℕ) : ℤ)) < Cardinal.aleph0 :=
    lt_of_le_of_lt le_add_self (h2 ▸ Cardinal.natCast_lt_aleph0)
  obtain ⟨f, hf⟩ := Cardinal.lt_aleph0.mp hlt
  rw [hf] at h2
  rw [Module.finrank_eq_of_rank_eq hf]
  split_ifs at h2 with hmod
  · have hN : (2 * r + 2) / 12 = 1 + f := by exact_mod_cast h2
    simp only [Nat.ModEq] at hmod
    omega
  · have hN : (2 * r + 2) / 12 + 1 = 1 + f := by exact_mod_cast h2
    simp only [Nat.ModEq] at hmod
    omega

/-- **Eichler–Shimura dimension identity at level one**:
`dim H¹(SL₂(ℤ), Sym^{2r}(ℂ²) ⊗ det^twist) = 2 dim S_{2r+2}(SL₂(ℤ)) + 1` for `r ≥ 1`. -/
theorem finrank_H1_sym_eq_cuspForms (r : ℕ) (positive : 0 < r) (twist : ℤ) :
    Module.finrank ℂ (groupCohomology.H1 (symRep (2 * r) twist)) =
      2 * Module.finrank ℂ (CuspForm (SpecialLinearGroup.mapGL (n := Fin 2) (R := ℤ) ℝ).range
        ((2 * r + 2 : ℕ) : ℤ)) + 1 := by
  have h := finrank_H1_sym r positive twist
  rw [finrank_cuspForm_levelOne r positive]
  omega

end Formula

end TernaryPeriodPolynomials.Spectral.ModularSymDimension
