module

public import TernaryPeriodPolynomials.Polynomial.GLAction
public import TernaryPeriodPolynomials.ArithmeticGroup.GL3Congruence.Basic
public import TernaryPeriodPolynomials.SymmetricSpace.All.TopBoundaryPolynomial
public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.Apolar
public import TernaryPeriodPolynomials.ArithmeticCohomology.Duality.InvolutionLevel
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section


/-!
# L1: complex coefficients versus the rational representation of the geometric side

The cochain model uses the complex coefficient system `E = homogeneousAction n (-1)` on
`HomogeneousPoly n` (complex homogeneous polynomials), the geometric side (the original library) the
rational representation `polynomialCoefficients n e` of `principalSix`, built from the same
formulas over `ℚ`. This file shows that the former is the extension of scalars of the latter:

* `complexify`: coefficient extension `VQ n →ₗ[ℚ] VC n`, equivariant for every integral matrix
  (`complexify_integralAction`);
* `complexifyEquiv : ℂ ⊗[ℚ] VQ n ≃ₗ[ℂ] VC n` through the monomial bases, equivariant
  (`complexifyEquiv_equivariant`);
* `rationalCoefficientComponent_integral`: the model coefficient action of `rationalInclusion γ`, `γ` in
  the arithmetic level, is the complex action of the integral matrix `γ` (the character component is trivial).

The dual system: the twisted apolar pairing of the model (`dualPairing`) is the extension of scalars of
the rational form `BQ`, diagonal in the monomial basis with weights `∏ dᵢ! · 3^{d₂}`
(`dualPairing_complexify`); it is nondegenerate (`BQ_nondegenerate`) and invariant (`BQ_invariant`), so
`dualEquiv : VQ n ≃ (VQ n)^∨` and `dualComplexEquiv : ℂ ⊗ (VQ n)^∨ ≃ VC n` identify the model's dual
system `E ∘ φ` with the complexified contragredient (`dualRep_comparison`, `dualValue_dualRepresentation`
for the original library contragredient `dualRepresentation`). `principalSix_le_arithmeticLevel` places
`Γ(6)` in the arithmetic level.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

open GeneralEisenstein

abbrev VQ (n : ℕ) := TernaryPoly.PolynomialGLAction.HomogeneousPoly n
abbrev VC (n : ℕ) := GeneralEisenstein.HomogeneousPoly n

/-- Extension of scalars `ℚ → ℂ` on homogeneous polynomials of degree `n`. -/
def complexify (n : ℕ) : VQ n →ₗ[ℚ] VC n :=
  LinearMap.codRestrict ((MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n).restrictScalars ℚ)
    ((MvPolynomial.mapAlgHom (σ := Fin 3) (Algebra.ofId ℚ ℂ)).toLinearMap.comp
      (Submodule.subtype _)) (fun f => by
      refine (MvPolynomial.mem_homogeneousSubmodule (σ := Fin 3) (R := ℂ) n _).mpr ?_
      exact ((MvPolynomial.mem_homogeneousSubmodule (σ := Fin 3) (R := ℚ) n f.1).mp f.2).map
        (algebraMap ℚ ℂ))

theorem complexify_coe (n : ℕ) (f : VQ n) :
    ((complexify n f : VC n) : GeneralEisenstein.Poly) = MvPolynomial.map (algebraMap ℚ ℂ) f.1 :=
  rfl

section Basis

instance degreeFinite (n : ℕ) : Finite {d : Fin 3 →₀ ℕ // d.degree = n} := by
  have hle : ∀ d : {d : Fin 3 →₀ ℕ // d.degree = n}, ∀ i, d.1 i ≤ n := by
    intro d i
    have := d.2
    rw [Finsupp.degree_eq_sum] at this
    calc d.1 i ≤ ∑ j, d.1 j := Finset.single_le_sum (f := fun j => d.1 j)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      _ = n := this
  refine Finite.of_injective (fun d : {d : Fin 3 →₀ ℕ // d.degree = n} =>
    (fun i => (⟨d.1 i, Nat.lt_succ_of_le (hle d i)⟩ : Fin (n + 1)))) ?_
  intro d d' h
  apply Subtype.ext
  ext i
  exact congrArg Fin.val (congrFun h i)


variable (K : Type) [Field K] (n : ℕ)

/-- The monomials of degree `n` as elements of the homogeneous submodule. -/
def monomialVec (d : {d : Fin 3 →₀ ℕ // d.degree = n}) : MvPolynomial.homogeneousSubmodule (Fin 3) K n :=
  ⟨monomial d.1 (1 : K), by
    rw [mem_homogeneousSubmodule]
    exact isHomogeneous_monomial _ (by simpa [Finsupp.degree_eq_weight_one] using d.2)⟩

theorem monomialVec_span : ⊤ ≤ Submodule.span K (Set.range (monomialVec K n)) := by
  rintro ⟨q0, hq0⟩ _
  have hp : q0 ∈ Submodule.span K
      ((fun d => monomial d (1 : K)) '' {d : Fin 3 →₀ ℕ | d.degree = n}) := by
    have h := hq0
    rw [homogeneousSubmodule_eq_finsupp_supported, AddMonoidAlgebra.supported_eq_span_single] at h
    exact h
  have h2 : q0 ∈ Submodule.map (Submodule.subtype _)
      (Submodule.span K (Set.range (monomialVec K n))) := by
    rw [Submodule.map_span]
    have e : (Submodule.subtype (MvPolynomial.homogeneousSubmodule (Fin 3) K n)) '' Set.range (monomialVec K n) =
        (fun d => monomial d (1 : K)) '' {d : Fin 3 →₀ ℕ | d.degree = n} := by
      refine Set.ext fun q => ?_
      constructor
      · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
        exact ⟨d.1, d.2, rfl⟩
      · rintro ⟨d, hd, rfl⟩
        exact ⟨_, ⟨⟨d, hd⟩, rfl⟩, rfl⟩
    rw [e]
    exact hp
  obtain ⟨q, hq, hqp⟩ := h2
  have : q = ⟨q0, hq0⟩ := Subtype.ext hqp
  exact this ▸ hq

/-- Monomial basis of the homogeneous polynomials of degree `n` in three variables. -/
def monomialBasis :
    Module.Basis {d : Fin 3 →₀ ℕ // d.degree = n} K (MvPolynomial.homogeneousSubmodule (Fin 3) K n) :=
  Module.Basis.mk (v := monomialVec K n)
    (by
      apply LinearIndependent.of_comp (Submodule.subtype _)
      have h := (MvPolynomial.basisMonomials (Fin 3) K).linearIndependent
      exact h.comp (fun d : {d : Fin 3 →₀ ℕ // d.degree = n} => d.1) Subtype.val_injective)
    (monomialVec_span K n)


instance (n : ℕ) : Module.Finite ℚ (VQ n) := Module.Finite.of_basis (monomialBasis ℚ n)

end Basis

theorem map_linearForm (M : Matrix (Fin 3) (Fin 3) ℚ) (i : Fin 3) :
    MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.PolynomialGLAction.linearForm M i) =
      GeneralEisenstein.linearForm (M.map (algebraMap ℚ ℂ)) i := by
  simp [TernaryPoly.PolynomialGLAction.linearForm, GeneralEisenstein.linearForm]

theorem map_substitute (M : Matrix (Fin 3) (Fin 3) ℚ) (p : MvPolynomial (Fin 3) ℚ) :
    MvPolynomial.map (algebraMap ℚ ℂ) (TernaryPoly.PolynomialGLAction.substitute M p) =
      GeneralEisenstein.substitute (M.map (algebraMap ℚ ℂ))
        (MvPolynomial.map (algebraMap ℚ ℂ) p) := by
  unfold TernaryPoly.PolynomialGLAction.substitute GeneralEisenstein.substitute
  rw [MvPolynomial.map_bind₁]
  have hfun : (fun i => MvPolynomial.map (algebraMap ℚ ℂ)
      (TernaryPoly.PolynomialGLAction.linearForm M i)) =
      GeneralEisenstein.linearForm (M.map (algebraMap ℚ ℂ)) := funext (map_linearForm M)
  rw [hfun]


theorem complexify_integralAction (n : ℕ) (e : ℤ) (g : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (v : VQ n) :
    complexify n (TernaryPoly.PolynomialGLAction.integralAction n e g v) =
      GeneralEisenstein.homogeneousAction n e
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g) (complexify n v) := by
  apply Subtype.ext
  rw [complexify_coe, TernaryPoly.PolynomialGLAction.integralAction_coe,
    GeneralEisenstein.homogeneousAction_coe, GeneralEisenstein.action_apply,
    TernaryPoly.PolynomialGLAction.action_apply, complexify_coe]
  have hmat : ((Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g)⁻¹ :
      Matrix.GeneralLinearGroup (Fin 3) ℂ).val =
      (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)⁻¹ :
        Matrix.GeneralLinearGroup (Fin 3) ℚ).val).map (algebraMap ℚ ℂ) := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map, Matrix.inv_def]
  have hdet : GeneralEisenstein.determinantCharacter e
      (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g) =
      algebraMap ℚ ℂ (TernaryPoly.PolynomialGLAction.determinantCharacter e
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g)) := by
    simp only [GeneralEisenstein.determinantCharacter, TernaryPoly.PolynomialGLAction.determinantCharacter,
      MonoidHom.coe_mk, OneHom.coe_mk, map_zpow₀]
    congr 1
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.map, Units.coe_map]
    have h1 := RingHom.map_det (Int.castRingHom ℂ) (g : Matrix (Fin 3) (Fin 3) ℤ)
    have h2 := RingHom.map_det (Int.castRingHom ℚ) (g : Matrix (Fin 3) (Fin 3) ℤ)
    refine h1.symm.trans (Eq.trans ?_ (congrArg (algebraMap ℚ ℂ) h2))
    simp
  rw [hmat, hdet, MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, map_substitute]


theorem complexify_monomialVec (n : ℕ) (d : {d : Fin 3 →₀ ℕ // d.degree = n}) :
    complexify n (monomialVec ℚ n d) = monomialVec ℂ n d := by
  apply Subtype.ext
  simp [complexify_coe, monomialVec]

open TensorProduct

/-- `ℂ ⊗_ℚ VQ n ≃ VC n`: the complex homogeneous polynomials are the extension of scalars of the
rational ones. -/
def complexifyEquiv (n : ℕ) : ℂ ⊗[ℚ] VQ n ≃ₗ[ℂ] VC n :=
  (Algebra.TensorProduct.basis ℂ (monomialBasis ℚ n)).equiv (monomialBasis ℂ n) (Equiv.refl _)

theorem complexifyEquiv_tmul (n : ℕ) (c : ℂ) (v : VQ n) :
    complexifyEquiv n (c ⊗ₜ v) = c • complexify n v := by
  have h : (complexifyEquiv n).toLinearMap = LinearMap.liftBaseChange ℂ (complexify n) := by
    refine (Algebra.TensorProduct.basis ℂ (monomialBasis ℚ n)).ext fun i => ?_
    have hb : (Algebra.TensorProduct.basis ℂ (monomialBasis ℚ n)) i =
        1 ⊗ₜ monomialVec ℚ n i := by
      simp [Algebra.TensorProduct.basis_apply, monomialBasis]
    rw [LinearEquiv.coe_coe, complexifyEquiv, Module.Basis.equiv_apply]
    rw [hb, LinearMap.liftBaseChange_tmul, one_smul, complexify_monomialVec]
    simp [monomialBasis]
  have := congrArg (fun L => L (c ⊗ₜ v)) h
  simpa using this


/-- **The identification `ℂ ⊗_ℚ VQ ≃ VC` is equivariant for integral matrices.** -/
theorem complexifyEquiv_equivariant (n : ℕ) (e : ℤ) (g : Matrix.GeneralLinearGroup (Fin 3) ℤ)
    (x : ℂ ⊗[ℚ] VQ n) :
    complexifyEquiv n (LinearMap.baseChange ℂ (TernaryPoly.PolynomialGLAction.integralAction n e g) x) =
      GeneralEisenstein.homogeneousAction n e
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g) (complexifyEquiv n x) := by
  have h : (complexifyEquiv n).toLinearMap ∘ₗ
      LinearMap.baseChange ℂ (TernaryPoly.PolynomialGLAction.integralAction n e g) =
      GeneralEisenstein.homogeneousAction n e
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) g) ∘ₗ (complexifyEquiv n).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c v
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
      complexifyEquiv_tmul, map_smul, complexify_integralAction]
  exact congrArg (fun L => L x) h

/-- The cochain-model coefficient system `E` at an element of the arithmetic level is the complex
coefficient action of the same integral matrix. -/
theorem rationalCoefficientComponent_integral (n : ℕ) (γ : GeneralEisenstein.arithmeticLevel) :
    GeneralEisenstein.rationalCoefficientComponent n GeneralEisenstein.trivialCharacter
        (GeneralEisenstein.rationalInclusion γ) =
      GeneralEisenstein.homogeneousAction n (-1)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ.1) := by
  apply LinearMap.ext
  intro v
  have hg : (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ)
      (Matrix.GeneralLinearGroup.map (algebraMap ℚ ℝ) (GeneralEisenstein.rationalInclusion γ))) =
      Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ.1 := by
    apply Units.ext
    ext i j
    simp [GeneralEisenstein.rationalInclusion, Matrix.GeneralLinearGroup.map]
  change (1 : ℂ) • (GeneralEisenstein.homogeneousAction n (-1) _ v) = _
  rw [one_smul, hg]


section Dual

open TernaryPeriodPolynomials.Duality

theorem substitute_diag_monomial (d : Fin 3 →₀ ℕ) :
    GeneralEisenstein.substitute (Matrix.diagonal ![1, 1, 3]) (monomial d (1 : ℂ)) =
      monomial d ((3 : ℂ) ^ (d 2)) := by
  have hlin : ∀ i, GeneralEisenstein.linearForm (Matrix.diagonal ![1, 1, 3]) i =
      C ((![1, 1, 3] : Fin 3 → ℂ) i) * X i := by
    intro i
    unfold GeneralEisenstein.linearForm
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  unfold GeneralEisenstein.substitute
  rw [bind₁_monomial]
  simp only [hlin, mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
  rw [monomial_eq, map_one, one_mul, Finsupp.prod]
  congr 2
  have : ∏ x ∈ d.support, (![1, 1, 3] : Fin 3 → ℂ) x ^ d x =
      ∏ x : Fin 3, (![1, 1, 3] : Fin 3 → ℂ) x ^ d x := by
    apply Finset.prod_subset (Finset.subset_univ _)
    intro x _ hx
    rw [Finsupp.notMem_support_iff.mp hx, pow_zero]
  rw [this, Fin.prod_univ_three]
  simp


/-- The rational weight `∏ᵢ dᵢ! · 3^{d₂}` of a monomial in the twisted apolar pairing. -/
def wtQ (n : ℕ) (d : {d : Fin 3 →₀ ℕ // d.degree = n}) : ℚ :=
  ((∏ i, (d.1 i).factorial : ℕ) : ℚ) * 3 ^ (d.1 2)

theorem dualPairing_monomialVec (n : ℕ) (d d' : {d : Fin 3 →₀ ℕ // d.degree = n}) :
    dualPairing n (monomialVec ℂ n d) (monomialVec ℂ n d') =
      if d = d' then ((wtQ n d : ℚ) : ℂ) else 0 := by
  rw [dualPairing_apply, apolar_apply]
  change apolarPoly (monomial d.1 (1 : ℂ))
    (GeneralEisenstein.substitute complexLevelScale (monomial d'.1 (1 : ℂ))) = _
  rw [complexLevelScale_eq, substitute_diag_monomial, apolarPoly_monomial, coeff_monomial]
  by_cases h : d = d'
  · subst h
    simp [wtQ, apolarWeight]
  · have h' : d'.1 ≠ d.1 := fun e => h (Subtype.ext e.symm)
    simp [h, h']

/-- The rational form underlying the twisted apolar pairing: diagonal in the monomial basis. -/
def BQ (n : ℕ) : VQ n →ₗ[ℚ] VQ n →ₗ[ℚ] ℚ :=
  (monomialBasis ℚ n).constr ℚ (fun d => (monomialBasis ℚ n).constr ℚ
    (fun d' => if d = d' then wtQ n d else 0))

theorem BQ_basis (n : ℕ) (d d' : {d : Fin 3 →₀ ℕ // d.degree = n}) :
    BQ n (monomialVec ℚ n d) (monomialVec ℚ n d') = if d = d' then wtQ n d else 0 := by
  have h1 : monomialVec ℚ n d = monomialBasis ℚ n d := by simp [monomialBasis]
  have h2 : monomialVec ℚ n d' = monomialBasis ℚ n d' := by simp [monomialBasis]
  rw [h1, h2, BQ, Module.Basis.constr_basis, Module.Basis.constr_basis]

theorem dualPairing_complexify (n : ℕ) (v w : VQ n) :
    dualPairing n (complexify n v) (complexify n w) = ((BQ n v w : ℚ) : ℂ) := by
  have h : ((dualPairing n).restrictScalars₁₂ ℚ ℚ).compl₁₂ (complexify n) (complexify n) =
      (BQ n).compr₂ (Algebra.linearMap ℚ ℂ) := by
    refine (monomialBasis ℚ n).ext fun i => (monomialBasis ℚ n).ext fun j => ?_
    have hi : monomialBasis ℚ n i = monomialVec ℚ n i := by simp [monomialBasis]
    have hj : monomialBasis ℚ n j = monomialVec ℚ n j := by simp [monomialBasis]
    simp only [LinearMap.compl₁₂_apply, LinearMap.compr₂_apply, LinearMap.restrictScalars₁₂_apply_apply,
      hi, hj, complexify_monomialVec, dualPairing_monomialVec, BQ_basis]
    split_ifs <;> simp
  have := congrArg (fun L => L v w) h
  simpa using this

theorem complexify_injective (n : ℕ) : Function.Injective (complexify n) := by
  intro v w h
  apply Subtype.ext
  have h' := congrArg (fun x : VC n => (x : GeneralEisenstein.Poly)) h
  exact MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective h'

theorem BQ_symm (n : ℕ) (v w : VQ n) : BQ n v w = BQ n w v := by
  have h : BQ n = (BQ n).flip := by
    refine (monomialBasis ℚ n).ext fun i => (monomialBasis ℚ n).ext fun j => ?_
    have hi : monomialBasis ℚ n i = monomialVec ℚ n i := by simp [monomialBasis]
    have hj : monomialBasis ℚ n j = monomialVec ℚ n j := by simp [monomialBasis]
    simp only [LinearMap.flip_apply, hi, hj, BQ_basis]
    by_cases hij : i = j
    · subst hij; rfl
    · simp [hij, Ne.symm hij]
  exact congrArg (fun L => L v w) h

theorem BQ_left_nondegenerate (n : ℕ) (v : VQ n) (h : ∀ w, BQ n v w = 0) : v = 0 := by
  apply complexify_injective
  rw [map_zero]
  apply dualPairing_nondegenerate
  intro w
  have hb : dualPairing n (complexify n v) = 0 := by
    refine (monomialBasis ℂ n).ext fun d => ?_
    have hd : monomialBasis ℂ n d = complexify n (monomialVec ℚ n d) := by
      rw [complexify_monomialVec]; simp [monomialBasis]
    rw [hd, LinearMap.zero_apply, dualPairing_complexify, h, Rat.cast_zero]
  rw [hb]
  rfl

theorem BQ_invariant (n : ℕ) (γ γ' : GeneralEisenstein.arithmeticLevel)
    (h : GeneralEisenstein.rationalInclusion γ' =
      dualInvolution (GeneralEisenstein.rationalInclusion γ)) (v w : VQ n) :
    BQ n (TernaryPoly.PolynomialGLAction.integralAction n (-1) γ.1 v)
        (TernaryPoly.PolynomialGLAction.integralAction n (-1) γ'.1 w) = BQ n v w := by
  apply (algebraMap ℚ ℂ).injective
  change ((BQ n _ _ : ℚ) : ℂ) = ((BQ n v w : ℚ) : ℂ)
  rw [← dualPairing_complexify, ← dualPairing_complexify, complexify_integralAction,
    complexify_integralAction, ← rationalCoefficientComponent_integral,
    ← rationalCoefficientComponent_integral, h]
  exact dualPairing_invariant n GeneralEisenstein.trivialCharacter _ _ _

theorem BQ_nondegenerate (n : ℕ) : (BQ n).Nondegenerate :=
  ⟨fun v hv => BQ_left_nondegenerate n v hv,
   fun w hw => BQ_left_nondegenerate n w fun v => (BQ_symm n w v).trans (hw v)⟩

/-- The rational form identifies `VQ n` with its dual. -/
def dualEquiv (n : ℕ) : VQ n ≃ₗ[ℚ] Module.Dual ℚ (VQ n) := LinearMap.BilinForm.toDual (BQ n) (BQ_nondegenerate n)

theorem dualEquiv_apply (n : ℕ) (v w : VQ n) : dualEquiv n v w = BQ n v w := rfl

/-- The contragredient action of an integral matrix on the rational dual. -/
def dualAct (n : ℕ) (e : ℤ) (g : Matrix.GeneralLinearGroup (Fin 3) ℤ) :
    Module.Dual ℚ (VQ n) →ₗ[ℚ] Module.Dual ℚ (VQ n) :=
  (TernaryPoly.PolynomialGLAction.integralAction n e g⁻¹).dualMap

theorem dualEquiv_equivariant (n : ℕ) (γ γ' : GeneralEisenstein.arithmeticLevel)
    (h : GeneralEisenstein.rationalInclusion γ' =
      dualInvolution (GeneralEisenstein.rationalInclusion γ)) (w : VQ n) :
    dualAct n (-1) γ.1 (dualEquiv n w) =
      dualEquiv n (TernaryPoly.PolynomialGLAction.integralAction n (-1) γ'.1 w) := by
  apply LinearMap.ext
  intro v
  have hinv := BQ_invariant n γ γ' h
    (TernaryPoly.PolynomialGLAction.integralAction n (-1) (γ.1⁻¹) v) w
  have hv : TernaryPoly.PolynomialGLAction.integralAction n (-1) γ.1
      (TernaryPoly.PolynomialGLAction.integralAction n (-1) (γ.1⁻¹) v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hv] at hinv
  change BQ n w _ = BQ n _ v
  rw [BQ_symm n w, BQ_symm n _ v, hinv]

open TensorProduct in
/-- `ℂ ⊗_ℚ (VQ n)^∨ ≃ VC n`, through the rational twisted apolar form. -/
def dualComplexEquiv (n : ℕ) : ℂ ⊗[ℚ] Module.Dual ℚ (VQ n) ≃ₗ[ℂ] VC n :=
  (LinearEquiv.baseChange ℚ ℂ _ _ (dualEquiv n).symm).trans (complexifyEquiv n)

open TensorProduct in
theorem dualComplexEquiv_equivariant (n : ℕ) (γ γ' : GeneralEisenstein.arithmeticLevel)
    (h : GeneralEisenstein.rationalInclusion γ' =
      dualInvolution (GeneralEisenstein.rationalInclusion γ)) (x : ℂ ⊗[ℚ] Module.Dual ℚ (VQ n)) :
    dualComplexEquiv n (LinearMap.baseChange ℂ (dualAct n (-1) γ.1) x) =
      GeneralEisenstein.homogeneousAction n (-1)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ'.1) (dualComplexEquiv n x) := by
  have key : (dualComplexEquiv n).toLinearMap ∘ₗ LinearMap.baseChange ℂ (dualAct n (-1) γ.1) =
      GeneralEisenstein.homogeneousAction n (-1)
        (Matrix.GeneralLinearGroup.map (Int.castRingHom ℂ) γ'.1) ∘ₗ
        (dualComplexEquiv n).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c f
    obtain ⟨w, rfl⟩ := (dualEquiv n).surjective f
    have e1 : dualAct n (-1) γ.1 (dualEquiv n w) =
        dualEquiv n (TernaryPoly.PolynomialGLAction.integralAction n (-1) γ'.1 w) :=
      dualEquiv_equivariant n γ γ' h w
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, e1,
      dualComplexEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
      LinearEquiv.symm_apply_apply, complexifyEquiv_tmul, map_smul, complexify_integralAction]
  exact congrArg (fun L => L x) key

/-- **The dual coefficient system is the extension of scalars of the contragredient.** The
model's `E ∘ φ`, at an element of the arithmetic level, is the complexification of the contragredient
action of `γ` on `(VQ n)^∨`. -/
theorem dualRep_comparison (n : ℕ) (γ : GeneralEisenstein.arithmeticLevel)
    (x : ℂ ⊗[ℚ] Module.Dual ℚ (VQ n)) :
    dualComplexEquiv n (LinearMap.baseChange ℂ (dualAct n (-1) γ.1) x) =
      (GeneralEisenstein.rationalCoefficientComponent n GeneralEisenstein.trivialCharacter)
        (dualInvolution (GeneralEisenstein.rationalInclusion γ)) (dualComplexEquiv n x) := by
  obtain ⟨γ', hγ'⟩ : ∃ γ' : GeneralEisenstein.arithmeticLevel,
      GeneralEisenstein.rationalInclusion γ' =
        dualInvolution (GeneralEisenstein.rationalInclusion γ) :=
    dualInvolution_mem_rationalLevel (g := GeneralEisenstein.rationalInclusion γ) ⟨γ, rfl⟩
  rw [dualComplexEquiv_equivariant n γ γ' hγ', ← hγ', rationalCoefficientComponent_integral]

open TernaryPoly TernaryPoly.IntegralGL3Congruence in
/-- The principal-six group lies in the arithmetic level of the cochain model. -/
theorem principalSix_le_arithmeticLevel :
    principalSix ≤ GeneralEisenstein.arithmeticLevel := by
  intro g hg
  have h3 : g ∈ principalThree := principalSix_le_three hg
  have h1 : GeneralEisenstein.reductionThree g = 1 := h3
  change GeneralEisenstein.reductionThree g ∈ GeneralEisenstein.rowStabilizer
  rw [h1]
  exact one_mem _

open TernaryPoly TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceAllTopBoundary
  TernaryPoly.SingularLocalDuality in
/-- The contragredient of the geometric coefficient system is `dualAct`. -/
theorem dualValue_dualRepresentation (n : ℕ) (e : ℤ) (γ : principalSix)
    (f : TernaryPoly.SingularLocalDuality.dualRepresentation (polynomialCoefficients n e)) :
    TernaryPoly.SingularLocalDuality.dualValue
        ((TernaryPoly.SingularLocalDuality.dualRepresentation (polynomialCoefficients n e)).ρ γ f) =
      dualAct n e γ.1 (TernaryPoly.SingularLocalDuality.dualValue f) :=
  rfl

end Dual

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
