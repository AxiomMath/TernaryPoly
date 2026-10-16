module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DualDictionary

@[expose] public section


/-!
# General coercivity: the literal `ℂ`-linear dual of `Sym^n ℂ³`

`CHom n` is the space of homogeneous polynomials of degree `n` over `ℂ` as a genuine `ℂ`-vector space,
with the Hermitian Fischer inner product `⟨p, q⟩ = ∑_d d! conj(p_d) q_d`.  Its literal dual
`StrongDual ℂ (CHom n)` carries the operator norm, which by the complex Riesz theorem is the Fischer
norm (`toDual` is an isometry).  The dual representation `ρ*_ℂ(g) = ρ_ℂ(θ g)` of the development
corresponds, under the Riesz map, to the contragredient action `φ ↦ φ ∘ ρ_ℂ(g)⁻¹`
(`toDual_rhoC_theta`), and the dual flat-bundle metric `‖ρ*(g)⁻¹ φ‖` of the paper is the
Hermitian dual metric of the development (`dualNorm_metric_frame`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MvPolynomial TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric
open TernaryPoly.SymmetricSpacePositive (RealGL)
open TernaryPoly.SymmetricSpaceCharts TernaryPoly.PolynomialFormMetric

/-- The Hermitian Fischer product of complex polynomials (conjugate-linear in the first slot). -/
def hermF (p q : CPoly) : ℂ :=
  ∑ d ∈ p.support, (factorialWeight d : ℂ) * (starRingEnd ℂ) (p.coeff d) * q.coeff d

theorem hermF_eq_sum (p q : CPoly) {s : Finset Exponent} (hs : p.support ⊆ s) :
    hermF p q = ∑ d ∈ s, (factorialWeight d : ℂ) * (starRingEnd ℂ) (p.coeff d) * q.coeff d := by
  unfold hermF
  apply Finset.sum_subset hs
  intro d _ hd
  have : p.coeff d = 0 := by simpa using hd
  simp [this]

theorem hermF_self (p : CPoly) : hermF p p = (fischerC p : ℂ) := by
  unfold hermF fischerC
  push_cast
  apply Finset.sum_congr rfl
  intro d _
  rw [mul_assoc, Complex.normSq_eq_conj_mul_self]

theorem hermF_conj (p q : CPoly) : (starRingEnd ℂ) (hermF q p) = hermF p q := by
  classical
  rw [hermF_eq_sum q p (s := p.support ∪ q.support) Finset.subset_union_right,
    hermF_eq_sum p q (s := p.support ∪ q.support) Finset.subset_union_left, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

theorem hermF_add_left (p p' q : CPoly) : hermF (p + p') q = hermF p q + hermF p' q := by
  classical
  rw [hermF_eq_sum (p + p') q (s := p.support ∪ p'.support) (support_add),
    hermF_eq_sum p q (s := p.support ∪ p'.support) Finset.subset_union_left,
    hermF_eq_sum p' q (s := p.support ∪ p'.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, map_add]
  ring

theorem hermF_smul_left (c : ℂ) (p q : CPoly) : hermF (c • p) q = (starRingEnd ℂ) c * hermF p q := by
  rw [hermF_eq_sum (c • p) q (s := p.support) (support_smul), hermF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp
  ring

theorem hermF_add_right (p q q' : CPoly) : hermF p (q + q') = hermF p q + hermF p q' := by
  unfold hermF
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  ring

theorem hermF_smul_right (c : ℂ) (p q : CPoly) : hermF p (c • q) = c * hermF p q := by
  unfold hermF
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  simp
  ring

theorem fischerC_eq_zero {p : CPoly} (h : fischerC p = 0) : p = 0 := by
  rw [fischerC_eq] at h
  have h1 := (add_eq_zero_iff_of_nonneg (factorialPairing_self_nonneg _)
    (factorialPairing_self_nonneg _)).mp h
  have hr := (factorialPairing_self_eq_zero _).mp h1.1
  have hi := (factorialPairing_self_eq_zero _).mp h1.2
  rw [← pairPoly_rePoly_imPoly p, hr, hi]
  simp [pairPoly]

theorem fischerC_nonneg (p : CPoly) : 0 ≤ fischerC p := by
  rw [fischerC_eq]
  exact add_nonneg (factorialPairing_self_nonneg _) (factorialPairing_self_nonneg _)

theorem factorialPairing_sum_of_subset (p q : Poly) {s : Finset Exponent} (hs : p.support ⊆ s) :
    factorialPairing p q = ∑ d ∈ s, factorialWeight d * p.coeff d * q.coeff d := by
  rw [factorialPairing_sum]
  apply Finset.sum_subset hs
  intro d _ hd
  have : p.coeff d = 0 := by simpa using hd
  simp [this]

/-- The Hermitian Fischer product in terms of real and imaginary parts. -/
theorem hermF_eq_re_im (p q : CPoly) :
    hermF p q =
      ((factorialPairing (rePoly p) (rePoly q) + factorialPairing (imPoly p) (imPoly q) : ℝ) : ℂ) +
        Complex.I * ((factorialPairing (rePoly p) (imPoly q) -
          factorialPairing (imPoly p) (rePoly q) : ℝ) : ℂ) := by
  rw [factorialPairing_sum_of_subset (rePoly p) (rePoly q) (support_rePoly_subset p),
    factorialPairing_sum_of_subset (rePoly p) (imPoly q) (support_rePoly_subset p),
    factorialPairing_sum_of_subset (imPoly p) (rePoly q) (support_imPoly_subset p),
    factorialPairing_sum_of_subset (imPoly p) (imPoly q) (support_imPoly_subset p)]
  unfold hermF
  push_cast
  simp only [coeff_rePoly, coeff_imPoly]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  have hp : p.coeff d = (p.coeff d).re + Complex.I * (p.coeff d).im := by
    apply Complex.ext <;> simp
  have hq : q.coeff d = (q.coeff d).re + Complex.I * (q.coeff d).im := by
    apply Complex.ext <;> simp
  conv_lhs => rw [hp, hq]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-(↑(factorialWeight d) * ((p.coeff d).im * (q.coeff d).im))) * hI

/-- Adjointness of real substitution for the Hermitian Fischer product. -/
theorem hermF_complexSubstitute (A : Matrix (Fin 3) (Fin 3) ℝ) (p q : CPoly) :
    hermF p (complexSubstitute A q) = hermF (complexSubstitute A.transpose p) q := by
  rw [hermF_eq_re_im, hermF_eq_re_im, rePoly_complexSubstitute, imPoly_complexSubstitute,
    rePoly_complexSubstitute, imPoly_complexSubstitute]
  have a1 : ∀ a c : Poly, factorialPairing a (realSubstitute A c) =
      factorialPairing (realSubstitute A.transpose a) c := by
    intro a c
    rw [realSubstitute_transpose_adjoint, Matrix.transpose_transpose]
  simp only [a1]

/-! ### The literal complex space and its Hermitian inner product -/

/-- Homogeneous polynomials of degree `n` over `ℂ`, as a genuine `ℂ`-vector space. -/
def CHom (n : ℕ) : Type := ↥(homogeneousSubmodule (Fin 3) ℂ n)

instance (n : ℕ) : AddCommGroup (CHom n) :=
  inferInstanceAs (AddCommGroup ↥(homogeneousSubmodule (Fin 3) ℂ n))

instance (n : ℕ) : Module ℂ (CHom n) :=
  inferInstanceAs (Module ℂ ↥(homogeneousSubmodule (Fin 3) ℂ n))

/-- The underlying polynomial. -/
def CHom.val {n : ℕ} (p : CHom n) : CPoly := Subtype.val (p : ↥(homogeneousSubmodule (Fin 3) ℂ n))

/-- Build an element from a homogeneous polynomial. -/
def CHom.mk {n : ℕ} (p : CPoly) (h : p.IsHomogeneous n) : CHom n :=
  (⟨p, (mem_homogeneousSubmodule _ _).2 h⟩ : ↥(homogeneousSubmodule (Fin 3) ℂ n))

theorem CHom.isHomogeneous {n : ℕ} (p : CHom n) : p.val.IsHomogeneous n :=
  (mem_homogeneousSubmodule _ _).1 (p : ↥(homogeneousSubmodule (Fin 3) ℂ n)).2

@[ext] theorem CHom.ext {n : ℕ} {p q : CHom n} (h : p.val = q.val) : p = q :=
  Subtype.ext h

@[simp] theorem CHom.val_mk {n : ℕ} (p : CPoly) (h : p.IsHomogeneous n) : (CHom.mk p h).val = p := rfl

@[simp] theorem CHom.val_add {n : ℕ} (p q : CHom n) : (p + q).val = p.val + q.val := rfl

@[simp] theorem CHom.val_smul {n : ℕ} (c : ℂ) (p : CHom n) : (c • p).val = c • p.val := rfl

@[simp] theorem CHom.val_zero {n : ℕ} : (0 : CHom n).val = 0 := rfl

@[simp] theorem CHom.val_sub {n : ℕ} (p q : CHom n) : (p - q).val = p.val - q.val := rfl

/-- The Hermitian Fischer inner product on `CHom n`. -/
@[instance_reducible] def chomCore (n : ℕ) : InnerProductSpace.Core ℂ (CHom n) where
  inner p q := hermF p.val q.val
  conj_inner_symm p q := hermF_conj p.val q.val
  re_inner_nonneg p := by
    change 0 ≤ (hermF p.val p.val).re
    rw [hermF_self]
    exact fischerC_nonneg _
  add_left p p' q := hermF_add_left p.val p'.val q.val
  smul_left p q c := hermF_smul_left c p.val q.val
  definite p h := by
    apply CHom.ext
    have h' : hermF p.val p.val = 0 := h
    rw [hermF_self] at h'
    exact fischerC_eq_zero (by exact_mod_cast h')

instance (n : ℕ) : NormedAddCommGroup (CHom n) :=
  let : InnerProductSpace.Core ℂ (CHom n) := chomCore n
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)

instance (n : ℕ) : InnerProductSpace ℂ (CHom n) :=
  InnerProductSpace.ofCore (chomCore n).toCore

theorem chom_inner (n : ℕ) (p q : CHom n) : inner ℂ p q = hermF p.val q.val := rfl

theorem chom_norm_sq (n : ℕ) (p : CHom n) : ‖p‖ ^ 2 = fischerC p.val := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p
  rw [chom_inner, hermF_self] at h
  have : ((‖p‖ : ℂ)) ^ 2 = (fischerC p.val : ℂ) := by simpa using h.symm
  exact_mod_cast this

/-- The identity on underlying polynomials, `CHom n ≃ₗ[ℝ] ComplexCoefficients n`. -/
def chomEquiv (n : ℕ) : CHom n ≃ₗ[ℝ] ComplexCoefficients n where
  toFun p := ⟨p.val, (mem_homogeneousSubmodule _ _).2 p.isHomogeneous⟩
  map_add' p q := rfl
  map_smul' r p := by
    apply Subtype.ext
    change (↑r : ℂ) • p.val = r • p.val
    exact (algebraMap_smul ℂ r p.val).symm
  invFun p := CHom.mk p.1 ((mem_homogeneousSubmodule _ _).1 p.2)
  left_inv p := rfl
  right_inv p := rfl

instance (n : ℕ) : FiniteDimensional ℂ (CHom n) := by
  have : FiniteDimensional ℝ (CHom n) := LinearEquiv.finiteDimensional (chomEquiv n).symm
  exact Module.Finite.of_restrictScalars_finite ℝ ℂ (CHom n)

theorem chomEquiv_val (n : ℕ) (p : CHom n) : ((chomEquiv n p : ComplexCoefficients n) : CPoly) = p.val :=
  rfl

/-! ### The representation and the Riesz map -/

/-- The complexified substitution representation `ρ_ℂ(g)` as a `ℂ`-linear map of `CHom n`. -/
def rhoC (n : ℕ) (g : RealGL) : CHom n →ₗ[ℂ] CHom n where
  toFun p := CHom.mk (complexSubstitute ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) p.val)
    (complexSubstitute_isHomogeneous _ p.isHomogeneous)
  map_add' p q := by
    apply CHom.ext
    exact map_add (complexSubstitute ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ)) p.val q.val
  map_smul' c p := by
    apply CHom.ext
    exact map_smul (complexSubstitute ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ)) c p.val

@[simp] theorem rhoC_val (n : ℕ) (g : RealGL) (p : CHom n) :
    (rhoC n g p).val = complexSubstitute ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) p.val := rfl

/-- `ρ_ℂ(θ g)` is the Hermitian adjoint of `ρ_ℂ(g)⁻¹`. -/
theorem inner_rhoC_theta (n : ℕ) (g : RealGL) (p q : CHom n) :
    inner ℂ (rhoC n (thetaHom g) p) q = inner ℂ p (rhoC n g⁻¹ q) := by
  rw [chom_inner, chom_inner, rhoC_val, rhoC_val]
  have e1 : (((thetaHom g)⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) =
      (g : Matrix (Fin 3) (Fin 3) ℝ).transpose := rfl
  have e2 : (((g⁻¹)⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [inv_inv]
  rw [e1, e2, hermF_complexSubstitute]

/-- **Riesz map and the contragredient action.**  Under the complex Riesz isomorphism
`toDual : CHom n ≃ₗᵢ⋆[ℂ] (CHom n →L[ℂ] ℂ)`, the dual representation `ρ_ℂ(θ g)` becomes the
contragredient action `φ ↦ φ ∘ ρ_ℂ(g)⁻¹`. -/
theorem toDual_rhoC_theta (n : ℕ) (g : RealGL) (p : CHom n) :
    InnerProductSpace.toDual ℂ (CHom n) (rhoC n (thetaHom g) p) =
      (InnerProductSpace.toDual ℂ (CHom n) p).comp (rhoC n g⁻¹).toContinuousLinearMap := by
  ext q
  simpa [InnerProductSpace.toDual_apply_apply] using inner_rhoC_theta n g p q

theorem rhoC_val_eq_representation (n : ℕ) (g : RealGL) (p : CHom n) :
    ((complexRepresentation n g (chomEquiv n p) : ComplexCoefficients n) : CPoly) =
      (rhoC n g p).val := rfl

theorem rhoC_inv_apply (n : ℕ) (g : RealGL) (p : CHom n) : rhoC n g⁻¹ (rhoC n g p) = p := by
  apply CHom.ext
  have h : complexRepresentation n g⁻¹ (complexRepresentation n g (chomEquiv n p)) =
      chomEquiv n p := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  exact congrArg (fun z : ComplexCoefficients n => (z : CPoly)) h

/-- The contragredient action is an isometry of the dual only for orthogonal `g` (the group `K`):
for `g gᵀ = 1` the representation `ρ_ℂ(g)` is unitary for the Hermitian Fischer product. -/
theorem rhoC_norm_of_orthogonal (n : ℕ) (g : RealGL)
    (hg : (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose = 1)
    (p : CHom n) : ‖rhoC n g p‖ = ‖p‖ := by
  have hinv : ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ).transpose := by
    rw [Matrix.coe_units_inv]
    exact Matrix.inv_eq_right_inv hg
  have hθ : thetaHom g = g := by
    apply Units.ext
    change ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ).transpose = _
    rw [hinv, Matrix.transpose_transpose]
  have h := inner_rhoC_theta n g p (rhoC n g p)
  rw [hθ, rhoC_inv_apply] at h
  have h1 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (rhoC n g p)
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) p
  rw [h] at h1
  have h3 : ((‖rhoC n g p‖ : ℂ)) ^ 2 = (‖p‖ : ℂ) ^ 2 := h1.symm.trans h2
  have h4 : ‖rhoC n g p‖ ^ 2 = ‖p‖ ^ 2 := by exact_mod_cast h3
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h4

/-- **The dual flat-bundle metric of the paper, literally.**  At a point whose
determinant-normalised form is `g gᵀ`, the norm `‖ρ*(g)⁻¹ φ‖` of an element `φ` of the `ℂ`-linear
dual of `Sym^n ℂ³` (with the dual operator norm and the contragredient action) is the Hermitian
dual coefficient metric used for the complex dual forms of the development. -/
theorem dualNorm_metric_frame {x : Coordinates} (hx : x ∈ positiveCoordinates)
    (g : RealGL)
    (hg : determinantNormalize (reconstruct x) =
      (g : Matrix (Fin 3) (Fin 3) ℝ) * (g : Matrix (Fin 3) (Fin 3) ℝ).transpose)
    (n : ℕ) (φ : StrongDual ℂ (CHom n)) :
    ‖φ.comp (rhoC n g).toContinuousLinearMap‖ ^ 2 =
      cplxBilin n (coordinateCoefficientBilin n (iotaC x))
        (chomEquiv n ((InnerProductSpace.toDual ℂ (CHom n)).symm φ))
        (chomEquiv n ((InnerProductSpace.toDual ℂ (CHom n)).symm φ)) := by
  set p := (InnerProductSpace.toDual ℂ (CHom n)).symm φ with hp
  have hφ : φ = InnerProductSpace.toDual ℂ (CHom n) p := by rw [hp]; simp
  have h1 := toDual_rhoC_theta n g⁻¹ p
  rw [inv_inv] at h1
  rw [hφ, ← h1, LinearIsometryEquiv.norm_map, chom_norm_sq,
    cplxBilin_iotaC_frame_self hx g hg]
  congr 1

/-- **Dual coercivity on the literal complex dual.**  The complex dual forms `CFormCxD` are forms
for the system `(ComplexCoefficients n, ρ_ℂ ∘ θ, Hermitian dual metric)`; by `toDual_rhoC_theta` and
`dualNorm_metric_frame` this system is the literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)` with the
contragredient action and the dual operator norm.  The coercivity theorem for it, with the same
constant, is therefore `general_coercivity_complex_dual` together with the metric identification. -/
theorem general_coercivity_complex_dual_literal (n : ℕ) (hn : 0 < n) :
    (∃ c : ℝ, 0 < c ∧ ∀ Γ : Subgroup RealGL, ∀ h : Admissible Γ,
      (∀ a : CFormCxD Γ n 0, c * normSqCxD a ≤ normSqCxD (CFormCxD.d h n 0 a)) ∧
        ∀ (k : ℕ) (a : CFormCxD Γ n (k + 1)) (e : CFormCxD Γ n k),
          IsCxDualFormalAdjoint h n k a e →
            c * normSqCxD a ≤ normSqCxD e + normSqCxD (CFormCxD.d h n (k + 1) a)) ∧
    (∀ (g : RealGL) (p : CHom n), InnerProductSpace.toDual ℂ (CHom n) (rhoC n (thetaHom g) p) =
        (InnerProductSpace.toDual ℂ (CHom n) p).comp (rhoC n g⁻¹).toContinuousLinearMap) :=
  ⟨general_coercivity_complex_dual n hn, fun g p => toDual_rhoC_theta n g p⟩

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
