module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Involution
public import Mathlib.Algebra.MvPolynomial.PDeriv

@[expose] public section


/-!
# The apolar pairing on ternary forms

The apolar pairing `⟨f, k⟩ = ∑ₘ (∏ᵢ mᵢ!) fₘ kₘ` is the constant `f(∂) k`. It satisfies
`⟨f ∘ M⁻¹, k ∘ Mᵀ⟩ = ⟨f, k⟩`, and twisting its second slot by `a = diag(1, 1, 3)` gives a
nondegenerate pairing between the coefficient representation and its pullback along
`dualInvolution`.
-/

noncomputable section

open GeneralEisenstein MvPolynomial Matrix

namespace TernaryPeriodPolynomials.Duality

/-- The factorial weight `∏ᵢ mᵢ!` of an exponent vector. -/
def apolarWeight (m : Fin 3 →₀ ℕ) : ℂ := ∏ i, ((m i).factorial : ℂ)

/-- Raising the `i`-th exponent multiplies the weight by `mᵢ + 1`. -/
theorem apolarWeight_add_single (m : Fin 3 →₀ ℕ) (i : Fin 3) :
    apolarWeight (m + Finsupp.single i 1) = apolarWeight m * ((m i : ℂ) + 1) := by
  unfold apolarWeight
  rw [Fin.prod_univ_three, Fin.prod_univ_three]
  fin_cases i <;> simp [Nat.factorial_succ] <;> ring

/-- The factorial weight never vanishes. -/
theorem apolarWeight_ne_zero (m : Fin 3 →₀ ℕ) : apolarWeight m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- The underlying function of the apolar pairing, summed over the support of `f`. -/
def apolarSum (f k : Poly) : ℂ := ∑ m ∈ f.support, apolarWeight m * f.coeff m * k.coeff m

/-- The apolar sum may be taken over any finite superset of the support. -/
theorem apolarSum_eq_of_subset (f k : Poly) {s : Finset (Fin 3 →₀ ℕ)} (hs : f.support ⊆ s) :
    apolarSum f k = ∑ m ∈ s, apolarWeight m * f.coeff m * k.coeff m := by
  apply Finset.sum_subset hs
  intro m _ hm
  rw [notMem_support_iff.mp hm, mul_zero, zero_mul]

/-- The apolar pairing `⟨f, k⟩ = ∑ₘ (∏ᵢ mᵢ!) fₘ kₘ` on all ternary polynomials. -/
def apolarPoly : Poly →ₗ[ℂ] Poly →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ apolarSum
    (by
      intro f f' k
      rw [apolarSum_eq_of_subset f k Finset.subset_union_left,
        apolarSum_eq_of_subset f' k Finset.subset_union_right,
        apolarSum_eq_of_subset (f + f') k support_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      ring)
    (by
      intro c f k
      rw [apolarSum_eq_of_subset (c • f) k support_smul,
        apolarSum_eq_of_subset f k le_rfl, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      simp only [coeff_smul, smul_eq_mul]
      ring)
    (by
      intro f k k'
      rw [apolarSum, apolarSum, apolarSum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intros
      simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      ring)
    (by
      intro c f k
      rw [apolarSum, apolarSum, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros
      simp only [coeff_smul, smul_eq_mul]
      ring)

/-- Unfolding the apolar pairing on polynomials. -/
theorem apolarPoly_apply (f k : Poly) :
    apolarPoly f k = ∑ m ∈ f.support, apolarWeight m * f.coeff m * k.coeff m := rfl

/-- The apolar pairing of a monomial with an arbitrary polynomial. -/
theorem apolarPoly_monomial (m : Fin 3 →₀ ℕ) (a : ℂ) (k : Poly) :
    apolarPoly (monomial m a) k = apolarWeight m * a * k.coeff m := by
  rw [apolarPoly_apply, ← apolarSum, apolarSum_eq_of_subset _ k support_monomial_subset,
    Finset.sum_singleton, coeff_monomial, ite_eq_left rfl]

/-- Pairing with a constant picks out the constant coefficient. -/
theorem apolarPoly_C (a : ℂ) (k : Poly) : apolarPoly (C a) k = a * constantCoeff k := by
  rw [← monomial_zero', apolarPoly_monomial, apolarWeight]
  simp [constantCoeff]

/-- Multiplication by `Xᵢ` is adjoint to `∂ᵢ` for the apolar pairing. -/
theorem apolarPoly_X_mul (i : Fin 3) (f k : Poly) :
    apolarPoly (X i * f) k = apolarPoly f (pderiv i k) := by
  induction f using MvPolynomial.induction_on' with
  | monomial m a =>
    rw [X, monomial_mul_monomial, one_mul, add_comm, apolarPoly_monomial, apolarPoly_monomial,
      coeff_pderiv, apolarWeight_add_single]
    ring
  | add p q hp hq =>
    rw [mul_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hp, hq]

/-- The chain rule for a linear substitution. -/
theorem pderiv_substitute (N : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) (k : Poly) :
    pderiv j (substitute N k) = ∑ l, C (N l j) * substitute N (pderiv l k) := by
  induction k using MvPolynomial.induction_on with
  | C a => simp [substitute]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hlin : pderiv j (linearForm N n) = C (N n j) := by
      simp [linearForm, pderiv_X, Pi.single_apply]
    have hs : ∑ l, C (N l j) * substitute N (p * pderiv l (X n)) =
        substitute N p * C (N n j) := by
      rw [Finset.sum_eq_single n]
      · rw [pderiv_X_self, mul_one, mul_comm]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl), mul_zero, map_zero, mul_zero]
      · simp
    rw [map_mul, substitute_X, pderiv_mul, hlin, hp, ← hs, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [pderiv_mul, map_add, map_mul (substitute N) (pderiv l p) (X n), substitute_X]
    ring

/-- Linear substitution preserves the constant coefficient. -/
theorem constantCoeff_substitute (N : Matrix (Fin 3) (Fin 3) ℂ) (k : Poly) :
    constantCoeff (substitute N k) = constantCoeff k := by
  induction k using MvPolynomial.induction_on with
  | C a => simp [substitute]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp => simp [hp, substitute_X, linearForm]

/-- The apolar pairing of an arbitrary polynomial with a monomial. -/
theorem apolarPoly_monomial_right (f : Poly) (m : Fin 3 →₀ ℕ) (a : ℂ) :
    apolarPoly f (monomial m a) = apolarWeight m * f.coeff m * a := by
  induction f using MvPolynomial.induction_on' with
  | monomial m' b =>
    rw [apolarPoly_monomial]
    by_cases hm : m' = m
    · subst hm
      rw [coeff_monomial, coeff_monomial, ite_eq_left rfl, ite_eq_left rfl]
    · rw [coeff_monomial, coeff_monomial, ite_eq_right hm, ite_eq_right (Ne.symm hm)]
      ring
  | add p q hp hq => rw [map_add, LinearMap.add_apply, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]; ring

/-- The apolar pairing is invariant under `(f, k) ↦ (f ∘ A, k ∘ B)` whenever `A Bᵀ = 1`. -/
theorem apolarPoly_substitute (A B : Matrix (Fin 3) (Fin 3) ℂ) (h : A * Bᵀ = 1) (f k : Poly) :
    apolarPoly (substitute A f) (substitute B k) = apolarPoly f k := by
  induction f using MvPolynomial.induction_on generalizing k with
  | C a =>
    rw [show substitute A (C a) = C a from (substitute A).commutes a, apolarPoly_C, apolarPoly_C,
      constantCoeff_substitute]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | mul_X p n hp =>
    have hcoef : ∀ l, ∑ j, A n j * B l j = if n = l then 1 else 0 := by
      intro l
      simpa [Matrix.mul_apply, Matrix.one_apply] using congrFun (congrFun h n) l
    calc apolarPoly (substitute A (p * X n)) (substitute B k)
        = ∑ j, A n j * apolarPoly (X j * substitute A p) (substitute B k) := by
          rw [map_mul, substitute_X, linearForm, Finset.mul_sum, map_sum, LinearMap.sum_apply]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [mul_left_comm, C_mul', map_smul, LinearMap.smul_apply, smul_eq_mul,
            mul_comm (substitute A p)]
      _ = ∑ j, ∑ l, A n j * B l j * apolarPoly p (pderiv l k) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [apolarPoly_X_mul, pderiv_substitute, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [C_mul', map_smul, hp, smul_eq_mul, mul_assoc]
      _ = apolarPoly p (pderiv n k) := by
          rw [Finset.sum_comm]
          simp_rw [← Finset.sum_mul, hcoef, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
            Finset.mem_univ, ite_true]
      _ = apolarPoly (p * X n) k := by rw [mul_comm, apolarPoly_X_mul]

/-- Linear substitution `f ↦ f ∘ M` as an endomorphism of degree-`n` forms. -/
def homogeneousSubstitute (n : ℕ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n :=
  (substitute M).toLinearMap.restrict fun _ hf =>
    (mem_homogeneousSubmodule n _).mpr
      (substitute_homogeneous M ((mem_homogeneousSubmodule n _).mp hf))

/-- The underlying polynomial of a homogeneous substitution. -/
@[simp] theorem homogeneousSubstitute_coe (n : ℕ) (M : Matrix (Fin 3) (Fin 3) ℂ)
    (f : HomogeneousPoly n) :
    ((homogeneousSubstitute n M f : HomogeneousPoly n) : Poly) = substitute M f := rfl

/-- The apolar pairing `⟨f, k⟩ = f(∂) k` on degree-`n` ternary forms. -/
def apolar (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ :=
  apolarPoly.compl₁₂ (HomogeneousPoly n).subtype (HomogeneousPoly n).subtype

/-- The degree-`n` apolar pairing is the restriction of `apolarPoly`. -/
theorem apolar_apply (n : ℕ) (f k : HomogeneousPoly n) :
    apolar n f k = apolarPoly (f : Poly) (k : Poly) := rfl

/-- The apolar pairing satisfies `⟨f ∘ M⁻¹, k ∘ Mᵀ⟩ = ⟨f, k⟩` for every `M ∈ GL₃(ℂ)`. -/
theorem apolar_invariant (n : ℕ) (M : GL3) (f k : HomogeneousPoly n) :
    apolar n (homogeneousSubstitute n ((M⁻¹ : GL3) : Matrix (Fin 3) (Fin 3) ℂ) f)
      (homogeneousSubstitute n (M : Matrix (Fin 3) (Fin 3) ℂ)ᵀ k) = apolar n f k :=
  apolarPoly_substitute _ _ (by rw [transpose_transpose]; exact M.inv_mul) f k

/-- The apolar pairing on degree-`n` forms is nondegenerate. -/
theorem apolar_nondegenerate {n : ℕ} (v : HomogeneousPoly n) (h : ∀ w, apolar n v w = 0) :
    v = 0 := by
  apply Subtype.ext
  ext m
  rw [Submodule.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  by_contra hm
  have hdeg := (mem_homogeneousSubmodule n _).mp v.2 hm
  have hw := h ⟨monomial m 1,
    (mem_homogeneousSubmodule n _).mpr (isWeightedHomogeneous_monomial 1 m 1 hdeg)⟩
  rw [apolar_apply, apolarPoly_monomial_right, mul_one] at hw
  exact hm ((mul_eq_zero.mp hw).resolve_left (apolarWeight_ne_zero m))

/-- The embedding `GL₃(ℚ) → GL₃(ℂ)` through `GL₃(ℝ)` used by the coefficient action. -/
def complexify : RationalGL3 →* GL3 :=
  (GeneralLinearGroup.map (algebraMap ℝ ℂ)).comp (GeneralLinearGroup.map (algebraMap ℚ ℝ))

/-- The complex image of `levelScale = diag(1, 1, 3)`. -/
def complexLevelScale : Matrix (Fin 3) (Fin 3) ℂ := (complexify levelScale : GL3)

/-- `complexLevelScale` is the diagonal matrix `diag(1, 1, 3)`. -/
theorem complexLevelScale_eq : complexLevelScale = Matrix.diagonal ![1, 1, 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexLevelScale, complexify, levelScale]

/-- The coefficient pairing twisted by `a = diag(1, 1, 3)`: `⟨v, w⟩ = ⟨v, w ∘ a⟩` (apolar). -/
def dualPairing (n : ℕ) : HomogeneousPoly n →ₗ[ℂ] HomogeneousPoly n →ₗ[ℂ] ℂ :=
  (apolar n).compl₂ (homogeneousSubstitute n complexLevelScale)

/-- Unfolding the twisted pairing. -/
theorem dualPairing_apply (n : ℕ) (v w : HomogeneousPoly n) :
    dualPairing n v w = apolar n v (homogeneousSubstitute n complexLevelScale w) := rfl

/-- The scalar `c(g) det(g)⁻¹` by which `rationalCoefficientComponent` twists substitution. -/
def coefficientScalar (χ : RankOneCharacter) : RationalGL3 →* ℂ :=
  (componentCharacter χ).comp (GeneralLinearGroup.map (algebraMap ℚ ℝ)) *
    (determinantCharacter (-1)).comp complexify

/-- The rational coefficient action is a scalar times the inverse substitution. -/
theorem rationalCoefficientComponent_coe (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3)
    (v : HomogeneousPoly n) :
    ((rationalCoefficientComponent n χ g v : HomogeneousPoly n) : Poly) =
      coefficientScalar χ g • substitute ((complexify g)⁻¹ : GL3) (v : Poly) := by
  rw [coefficientScalar, MonoidHom.mul_apply, mul_smul]
  rfl

/-- A ring map preserves determinant one. -/
theorem det_map_eq_one {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {x : GeneralLinearGroup (Fin 3) R} (hx : GeneralLinearGroup.det x = 1) :
    GeneralLinearGroup.det (GeneralLinearGroup.map f x) = 1 := by
  apply Units.ext
  have hx' : (x : Matrix (Fin 3) (Fin 3) R).det = 1 := congrArg Units.val hx
  simp only [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply, Units.val_one]
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hx', map_one]

/-- The coefficient scalar is trivial on determinant-one matrices. -/
theorem coefficientScalar_eq_one (χ : RankOneCharacter) {x : RationalGL3}
    (hx : GeneralLinearGroup.det x = 1) : coefficientScalar χ x = 1 := by
  have hR := det_map_eq_one (algebraMap ℚ ℝ) hx
  have hC : GeneralLinearGroup.det (complexify x) = 1 := det_map_eq_one (algebraMap ℝ ℂ) hR
  rw [coefficientScalar, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
    componentCharacter, MonoidHom.comp_apply, MonoidHom.comp_apply, hR, map_one, map_one, one_mul]
  change ((GeneralLinearGroup.det (complexify x) : ℂˣ) : ℂ) ^ (-1 : ℤ) = 1
  rw [hC, Units.val_one, one_zpow]

/-- The inverse transpose inverts the determinant. -/
theorem det_inverseTranspose (g : RationalGL3) :
    GeneralLinearGroup.det (inverseTranspose g) = (GeneralLinearGroup.det g)⁻¹ := by
  rw [← map_inv]
  apply Units.ext
  simp only [GeneralLinearGroup.val_det_apply]
  exact Matrix.det_transpose _

/-- The coefficient scalars of `g` and `dualInvolution g` are mutually inverse. -/
theorem coefficientScalar_dualInvolution_mul (χ : RankOneCharacter) (g : RationalGL3) :
    coefficientScalar χ (dualInvolution g) * coefficientScalar χ g = 1 := by
  rw [← map_mul]
  apply coefficientScalar_eq_one
  rw [dualInvolution_apply, map_mul, map_mul, map_mul, map_inv, det_inverseTranspose]
  simp [mul_comm, mul_assoc]

/-- The complex image of `inverseTranspose g⁻¹` is the transpose of that of `g`. -/
theorem complexify_inverseTranspose_inv (g : RationalGL3) :
    ((complexify (inverseTranspose g⁻¹) : GL3) : Matrix (Fin 3) (Fin 3) ℂ) =
      ((complexify g : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ := by
  simp only [complexify, MonoidHom.comp_apply, GeneralLinearGroup.val_map_apply]
  change ((((g⁻¹)⁻¹ : RationalGL3) : Matrix (Fin 3) (Fin 3) ℚ)ᵀ.map _).map _ = _
  rw [inv_inv, transpose_map, transpose_map]

/-- Over `ℂ`, `(dualInvolution g)⁻¹ a = a gᵀ` for `a = diag(1, 1, 3)`. -/
theorem complexify_dualInvolution_inv_mul (g : RationalGL3) :
    ((complexify (dualInvolution g))⁻¹ : GL3).val * complexLevelScale =
      complexLevelScale * ((complexify g : GL3) : Matrix (Fin 3) (Fin 3) ℂ)ᵀ := by
  have h : (complexify (dualInvolution g))⁻¹ * complexify levelScale =
      complexify levelScale * complexify (inverseTranspose g⁻¹) := by
    rw [← map_inv, ← map_mul, ← map_mul, dualInvolution_apply, map_inv inverseTranspose]
    congr 1
    group
  have h' := congrArg (fun x : GL3 => (x : Matrix (Fin 3) (Fin 3) ℂ)) h
  rw [complexLevelScale]
  simpa only [Units.val_mul, complexify_inverseTranspose_inv] using h'

/-- `dualPairing` pairs the coefficient representation with its pullback along `dualInvolution`. -/
theorem dualPairing_invariant (n : ℕ) (χ : RankOneCharacter) (g : RationalGL3)
    (v w : HomogeneousPoly n) :
    dualPairing n (rationalCoefficientComponent n χ g v)
      (rationalCoefficientComponent n χ (dualInvolution g) w) = dualPairing n v w := by
  rw [dualPairing_apply, dualPairing_apply, apolar_apply, apolar_apply, homogeneousSubstitute_coe,
    homogeneousSubstitute_coe, rationalCoefficientComponent_coe, rationalCoefficientComponent_coe,
    map_smul, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    mul_comm (coefficientScalar χ g), coefficientScalar_dualInvolution_mul, one_mul,
    ← AlgHom.comp_apply, substitute_comp, complexify_dualInvolution_inv_mul, ← substitute_comp,
    AlgHom.comp_apply]
  exact apolarPoly_substitute _ _ (by rw [transpose_transpose]; exact (complexify g).inv_mul) _ _

/-- `dualPairing` is nondegenerate in its first argument. -/
theorem dualPairing_nondegenerate {n : ℕ} (v : HomogeneousPoly n)
    (h : ∀ w, dualPairing n v w = 0) : v = 0 := by
  refine apolar_nondegenerate v fun w => ?_
  have hw : homogeneousSubstitute n complexLevelScale
      (homogeneousSubstitute n ((complexify levelScale)⁻¹ : GL3) w) = w := by
    apply Subtype.ext
    rw [homogeneousSubstitute_coe, homogeneousSubstitute_coe, ← AlgHom.comp_apply, substitute_comp,
      complexLevelScale, Units.inv_mul, substitute_one, AlgHom.id_apply]
  rw [← hw, ← dualPairing_apply]
  exact h _

end TernaryPeriodPolynomials.Duality
