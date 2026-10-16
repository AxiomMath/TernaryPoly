module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Basic
public import TernaryPeriodPolynomials.DifferentialForm.CoefficientMetric.Representation
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.SpecialLinear.GroupMetric

@[expose] public section


/-!
# General coercivity, complex coefficients: the real/imaginary bridge

The complexification of the coefficient bundle has fibre `Sym^n ℂ³`, the space of homogeneous
polynomials of degree `n` over `ℂ`, with the Hermitian Fischer norm
`‖p‖² = ∑_d d! |c_d|²` and the action of `GL₃(ℝ)` by substitution.  This file shows that taking
real and imaginary parts of the coefficients is an `ℝ`-linear isomorphism of this space with pairs of
elements of the real coefficient space `Coefficients n`, which intertwines the substitution actions and
carries the Hermitian Fischer norm to the sum of the two real Fischer norms.  This justifies the
description of complex-coefficient forms as pairs of real forms (`CFormC`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MvPolynomial TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric
open TernaryPoly.SymmetricSpacePositive (RealGL)

/-- Polynomials in three variables over `ℂ`. -/
abbrev CPoly := MvPolynomial (Fin 3) ℂ

/-- The polynomial whose coefficients are the real parts of those of `p`. -/
def rePoly (p : CPoly) : Poly := ∑ d ∈ p.support, monomial d (p.coeff d).re

/-- The polynomial whose coefficients are the imaginary parts of those of `p`. -/
def imPoly (p : CPoly) : Poly := ∑ d ∈ p.support, monomial d (p.coeff d).im

theorem coeff_rePoly (p : CPoly) (d : Exponent) : (rePoly p).coeff d = (p.coeff d).re := by
  classical
  unfold rePoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : d ∈ p.support
  · simp [h]
  · have : p.coeff d = 0 := by simpa using h
    simp [h, this]

theorem coeff_imPoly (p : CPoly) (d : Exponent) : (imPoly p).coeff d = (p.coeff d).im := by
  classical
  unfold imPoly
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  by_cases h : d ∈ p.support
  · simp [h]
  · have : p.coeff d = 0 := by simpa using h
    simp [h, this]

/-- The complex polynomial `q + i r` with real polynomials `q`, `r`. -/
def pairPoly (q r : Poly) : CPoly :=
  map (algebraMap ℝ ℂ) q + C Complex.I * map (algebraMap ℝ ℂ) r

theorem coeff_pairPoly (q r : Poly) (d : Exponent) :
    (pairPoly q r).coeff d = Complex.ofReal (q.coeff d) + Complex.I * Complex.ofReal (r.coeff d) := by
  simp [pairPoly, coeff_map, coeff_C_mul]

theorem pairPoly_rePoly_imPoly (p : CPoly) : pairPoly (rePoly p) (imPoly p) = p := by
  ext d
  rw [coeff_pairPoly, coeff_rePoly, coeff_imPoly]
  apply Complex.ext <;> simp

theorem rePoly_pairPoly (q r : Poly) : rePoly (pairPoly q r) = q := by
  ext d
  rw [coeff_rePoly, coeff_pairPoly]
  simp

theorem imPoly_pairPoly (q r : Poly) : imPoly (pairPoly q r) = r := by
  ext d
  rw [coeff_imPoly, coeff_pairPoly]
  simp

/-! ### Substitution by real matrices -/

/-- The linear form `∑ⱼ Aᵢⱼ Xⱼ` with complex-polynomial values. -/
def complexLinearForm (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) : CPoly := ∑ j, C (Complex.ofReal (A i j)) * X j

/-- Substitution of the linear forms of a real matrix in a complex polynomial. -/
def complexSubstitute (A : Matrix (Fin 3) (Fin 3) ℝ) : CPoly →ₐ[ℂ] CPoly := bind₁ (complexLinearForm A)

theorem complexSubstitute_map (A : Matrix (Fin 3) (Fin 3) ℝ) (q : Poly) :
    complexSubstitute A (map (algebraMap ℝ ℂ) q) = map (algebraMap ℝ ℂ) (realSubstitute A q) := by
  have h := map_bind₁ (algebraMap ℝ ℂ) (realLinearForm A) q
  change _ = map (algebraMap ℝ ℂ) (bind₁ (realLinearForm A) q)
  rw [h]
  have hform : complexLinearForm A = fun i => map (algebraMap ℝ ℂ) (realLinearForm A i) := by
    funext i
    simp [complexLinearForm, realLinearForm, map_sum, map_mul]
  change bind₁ (complexLinearForm A) _ = _
  rw [hform]

theorem complexSubstitute_pairPoly (A : Matrix (Fin 3) (Fin 3) ℝ) (q r : Poly) :
    complexSubstitute A (pairPoly q r) = pairPoly (realSubstitute A q) (realSubstitute A r) := by
  unfold pairPoly
  rw [map_add, map_mul, complexSubstitute_map, complexSubstitute_map]
  congr 2
  simp [complexSubstitute]

theorem rePoly_complexSubstitute (A : Matrix (Fin 3) (Fin 3) ℝ) (p : CPoly) :
    rePoly (complexSubstitute A p) = realSubstitute A (rePoly p) := by
  conv_lhs => rw [← pairPoly_rePoly_imPoly p]
  rw [complexSubstitute_pairPoly, rePoly_pairPoly]

theorem imPoly_complexSubstitute (A : Matrix (Fin 3) (Fin 3) ℝ) (p : CPoly) :
    imPoly (complexSubstitute A p) = realSubstitute A (imPoly p) := by
  conv_lhs => rw [← pairPoly_rePoly_imPoly p]
  rw [complexSubstitute_pairPoly, imPoly_pairPoly]

/-! ### The Hermitian Fischer norm -/

/-- The Hermitian Fischer norm squared `∑_d d! |c_d|²` of a complex polynomial. -/
def fischerC (p : CPoly) : ℝ := ∑ d ∈ p.support, factorialWeight d * Complex.normSq (p.coeff d)

theorem support_rePoly_subset (p : CPoly) : (rePoly p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, coeff_rePoly] at hd
  rw [mem_support_iff]
  intro h0
  apply hd
  simp [h0]

theorem support_imPoly_subset (p : CPoly) : (imPoly p).support ⊆ p.support := by
  intro d hd
  rw [mem_support_iff, coeff_imPoly] at hd
  rw [mem_support_iff]
  intro h0
  apply hd
  simp [h0]

theorem factorialPairing_self_sum {q : Poly} {s : Finset Exponent} (hs : q.support ⊆ s) :
    factorialPairing q q = ∑ d ∈ s, factorialWeight d * q.coeff d * q.coeff d := by
  rw [factorialPairing_sum]
  apply Finset.sum_subset hs
  intro d _ hd
  have : q.coeff d = 0 := by simpa using hd
  simp [this]

theorem fischerC_eq (p : CPoly) :
    fischerC p = factorialPairing (rePoly p) (rePoly p) + factorialPairing (imPoly p) (imPoly p) := by
  rw [factorialPairing_self_sum (support_rePoly_subset p),
    factorialPairing_self_sum (support_imPoly_subset p), ← Finset.sum_add_distrib]
  unfold fischerC
  apply Finset.sum_congr rfl
  intro d _
  rw [coeff_rePoly, coeff_imPoly, Complex.normSq_apply]
  ring

/-! ### Homogeneity -/

theorem isHomogeneous_rePoly {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (rePoly p).IsHomogeneous n := by
  intro d hd
  apply hp
  rw [coeff_rePoly] at hd
  intro h0
  apply hd
  simp [h0]

theorem isHomogeneous_imPoly {p : CPoly} {n : ℕ} (hp : p.IsHomogeneous n) :
    (imPoly p).IsHomogeneous n := by
  intro d hd
  apply hp
  rw [coeff_imPoly] at hd
  intro h0
  apply hd
  simp [h0]

theorem isHomogeneous_pairPoly {q r : Poly} {n : ℕ} (hq : q.IsHomogeneous n)
    (hr : r.IsHomogeneous n) : (pairPoly q r).IsHomogeneous n := by
  intro d hd
  rw [coeff_pairPoly] at hd
  by_cases h : q.coeff d = 0
  · apply hr
    intro h0
    apply hd
    simp [h, h0]
  · exact hq h

/-! ### The isomorphism with pairs of real coefficients -/

/-- The complexified coefficient space `Sym^n ℂ³` (homogeneous polynomials of degree `n` over `ℂ`),
as a real vector space. -/
abbrev ComplexCoefficients (n : ℕ) : Submodule ℝ CPoly :=
  (homogeneousSubmodule (Fin 3) ℂ n).restrictScalars ℝ

theorem mem_complexCoefficients {n : ℕ} {p : CPoly} :
    p ∈ ComplexCoefficients n ↔ p.IsHomogeneous n := mem_homogeneousSubmodule _ _

/-- **Real and imaginary parts.**  The complexified coefficient space is isomorphic, as a real vector
space, to pairs of real coefficient polynomials. -/
def reImEquiv (n : ℕ) : ComplexCoefficients n ≃ₗ[ℝ] Coefficients n × Coefficients n where
  toFun p := (⟨rePoly p.1, (mem_homogeneousSubmodule _ _).2
      (isHomogeneous_rePoly ((mem_homogeneousSubmodule _ _).1 p.2))⟩,
    ⟨imPoly p.1, (mem_homogeneousSubmodule _ _).2
      (isHomogeneous_imPoly ((mem_homogeneousSubmodule _ _).1 p.2))⟩)
  map_add' p q := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext d
      simp [coeff_rePoly]
    · ext d
      simp [coeff_imPoly]
  map_smul' r p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext d
      simp [coeff_rePoly]
    · ext d
      simp [coeff_imPoly]
  invFun qr := ⟨pairPoly qr.1.1 qr.2.1, (mem_homogeneousSubmodule _ _).2
      (isHomogeneous_pairPoly ((mem_homogeneousSubmodule _ _).1 qr.1.2)
        ((mem_homogeneousSubmodule _ _).1 qr.2.2))⟩
  left_inv p := Subtype.ext (pairPoly_rePoly_imPoly p.1)
  right_inv qr := Prod.ext (Subtype.ext (rePoly_pairPoly _ _)) (Subtype.ext (imPoly_pairPoly _ _))

/-- The Hermitian Fischer norm of a complex coefficient is the sum of the real Fischer norms of its
real and imaginary parts. -/
theorem fischerC_reImEquiv (n : ℕ) (p : ComplexCoefficients n) :
    fischerC p.1 = ‖(reImEquiv n p).1‖ ^ 2 + ‖(reImEquiv n p).2‖ ^ 2 := by
  rw [fischerC_eq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, coefficient_inner,
    coefficient_inner]
  rfl

theorem complexSubstitute_isHomogeneous (B : Matrix (Fin 3) (Fin 3) ℝ) {p : CPoly} {n : ℕ}
    (hp : p.IsHomogeneous n) : (complexSubstitute B p).IsHomogeneous n := by
  rw [← pairPoly_rePoly_imPoly p, complexSubstitute_pairPoly]
  exact isHomogeneous_pairPoly (realSubstitute_preserves_degree B (isHomogeneous_rePoly hp))
    (realSubstitute_preserves_degree B (isHomogeneous_imPoly hp))

/-- The action of `g ∈ GL₃(ℝ)` on the complexified coefficient space by substitution of the inverse
matrix, `p ↦ p ∘ g⁻¹`. -/
def complexRho (n : ℕ) (g : RealGL) : ComplexCoefficients n →ₗ[ℝ] ComplexCoefficients n where
  toFun p := ⟨complexSubstitute ((g⁻¹ : RealGL) : Matrix (Fin 3) (Fin 3) ℝ) p.1,
    (mem_homogeneousSubmodule _ _).2 (complexSubstitute_isHomogeneous _
      ((mem_homogeneousSubmodule _ _).1 p.2))⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r p := Subtype.ext (AlgHom.map_smul_of_tower (complexSubstitute _) r p.1)

/-- The substitution action on `Sym^n ℂ³` corresponds, under the real/imaginary-part isomorphism, to
the real substitution action on both components. -/
theorem reImEquiv_complexRho (n : ℕ) (g : RealGL) (p : ComplexCoefficients n) :
    reImEquiv n (complexRho n g p) =
      (realHomogeneousAction n g (reImEquiv n p).1, realHomogeneousAction n g (reImEquiv n p).2) :=
  Prod.ext (Subtype.ext (rePoly_complexSubstitute _ _)) (Subtype.ext (imPoly_complexSubstitute _ _))

/-! ### Normed structure and the representation -/

/-- An auxiliary norm on `ComplexCoefficients n`, induced from the product of the two real
coefficient norms through `reImEquiv` (so it is a *maximum* of the real and imaginary norms, not the
Hermitian norm `√(fischerC)`).  It is used only to give the space a topology and a
finite-dimensional structure for the smoothness of forms; the two norms are equivalent and induce
the same (unique) topology.  The metric that all `L²` norms of complex forms are built from is the
Hermitian one, `fischerC` / `cplxBilin`, carried explicitly through the form pairing
(`formPairingC`, `l2Cx`) in `ComplexForms.lean`. -/
instance complexCoefficientsNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (ComplexCoefficients n) :=
  NormedAddCommGroup.induced _ _ (reImEquiv n) (reImEquiv n).injective

instance complexCoefficientsNormedSpace (n : ℕ) : NormedSpace ℝ (ComplexCoefficients n) :=
  NormedSpace.induced ℝ _ _ (reImEquiv n)

/-- The topology of the complex coefficient space is the one of its norm. -/
instance (priority := high) complexCoefficientsTopologicalSpace (n : ℕ) :
    TopologicalSpace (ComplexCoefficients n) :=
  (complexCoefficientsNormedAddCommGroup n).toMetricSpace.toUniformSpace.toTopologicalSpace

instance complexCoefficientsFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (ComplexCoefficients n) :=
  LinearEquiv.finiteDimensional (reImEquiv n).symm

/-- The auxiliary norm is the product max-norm of the real and imaginary parts; it is *not* the
Hermitian Fischer norm (see `fischerC_reImEquiv` for that one). -/
theorem norm_complexCoefficients (n : ℕ) (p : ComplexCoefficients n) :
    ‖p‖ = ‖reImEquiv n p‖ := rfl

/-- Real and imaginary parts as a continuous linear equivalence. -/
def reImCLE (n : ℕ) : ComplexCoefficients n ≃L[ℝ] Coefficients n × Coefficients n :=
  (reImEquiv n).toContinuousLinearEquiv

/-- The representation of `GL₃(ℝ)` on the complexified coefficient space. -/
def complexRepresentation (n : ℕ) : Representation ℝ RealGL (ComplexCoefficients n) where
  toFun g := complexRho n g
  map_one' := LinearMap.ext fun p => (reImEquiv n).injective (by
    rw [reImEquiv_complexRho]
    simp)
  map_mul' g h := LinearMap.ext fun p => (reImEquiv n).injective (by
    change reImEquiv n (complexRho n (g * h) p) = reImEquiv n (complexRho n g (complexRho n h p))
    rw [reImEquiv_complexRho, reImEquiv_complexRho, reImEquiv_complexRho]
    simp)

theorem reImEquiv_complexRepresentation (n : ℕ) (g : RealGL) (p : ComplexCoefficients n) :
    reImEquiv n (complexRepresentation n g p) =
      (realHomogeneousAction n g (reImEquiv n p).1, realHomogeneousAction n g (reImEquiv n p).2) :=
  reImEquiv_complexRho n g p

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
