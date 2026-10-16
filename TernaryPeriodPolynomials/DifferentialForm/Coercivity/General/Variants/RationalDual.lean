module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringSingular

@[expose] public section


/-!
# The dual rational system is the contragredient

The rational Fischer (factorial monomial) pairing `ratPairing` on `ℚ[x₁,x₂,x₃]` is the rational form
of `TernaryPoly.SL3PolynomialCoercivity.factorialPairing` (`cast_ratPairing`).  It is positive
definite on degree-`n` homogeneous polynomials, hence identifies `Sym^n ℚ³` with its dual
(`fischerEquiv`), and by the transpose-adjoint identity (`ratPairing_substitute`) it intertwines the
dual action (`dualDeckCoefficientRep`, substitution of `gᵀ`) with the contragredient action
(`fischerEquiv_equivariant`).  So `dualDeckCoefficientRep n ≅ (rationalDeckCoefficientRep n 0)ᵛ` as
rational deck-group representations, and the genuine contragredient local system `Hom_ℚ(A, ℚ)`
satisfies the singular vanishing `contragredient_compactForget_zero` (and its complexification).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open MvPolynomial TernaryPoly.SL3PolynomialCoercivity TernaryPoly.PolynomialCoefficientMetric

/-- Rational polynomials in three variables. -/
abbrev QPoly := MvPolynomial (Fin 3) ℚ

/-- The rational factorial weight `∏ (d i)!` of a monomial. -/
def ratWeight (d : Exponent) : ℚ := ∏ i : Fin 3, ((d i).factorial : ℚ)

/-- The rational Fischer (factorial monomial) pairing. -/
def ratPairing : QPoly →ₗ[ℚ] QPoly →ₗ[ℚ] ℚ :=
  (basisMonomials (Fin 3) ℚ).constr ℚ (fun d => ratWeight d • lcoeff ℚ d)

theorem ratPairing_monomial_one (d : Exponent) (q : QPoly) :
    ratPairing (monomial d 1) q = ratWeight d * q.coeff d := by
  have h := (basisMonomials (Fin 3) ℚ).constr_basis ℚ (fun d => ratWeight d • lcoeff ℚ d) d
  exact congrArg (fun f : QPoly →ₗ[ℚ] ℚ => f q) h

theorem cast_ratWeight (d : Exponent) : ((ratWeight d : ℚ) : ℝ) = factorialWeight d := by
  simp [ratWeight, factorialWeight]

theorem cast_ratPairing (p q : QPoly) :
    ((ratPairing p q : ℚ) : ℝ) =
      factorialPairing (MvPolynomial.map (algebraMap ℚ ℝ) p) (MvPolynomial.map (algebraMap ℚ ℝ) q) := by
  induction p using MvPolynomial.induction_on' with
  | monomial d a =>
    have h1 : monomial d a = a • (monomial d 1 : QPoly) := by simp [smul_monomial]
    have hl : ratPairing (monomial d a) q = a * ratWeight d * q.coeff d := by
      rw [h1, LinearMap.map_smul, LinearMap.smul_apply, ratPairing_monomial_one, smul_eq_mul]
      ring
    rw [hl, MvPolynomial.map_monomial, factorialPairing_monomial, coeff_map]
    push_cast
    rw [cast_ratWeight]
    simp
  | add p p' hp hp' =>
    rw [map_add, LinearMap.add_apply, Rat.cast_add, hp, hp']
    simp only [map_add, LinearMap.add_apply]


open TernaryPoly.PolynomialGLAction (substitute substitute_one substitute_comp) in
theorem ratPairing_substitute (M : Matrix (Fin 3) (Fin 3) ℚ) (p q : QPoly) :
    ratPairing (TernaryPoly.PolynomialGLAction.substitute M p) q =
      ratPairing p (TernaryPoly.PolynomialGLAction.substitute M.transpose q) := by
  apply Rat.cast_injective (α := ℝ)
  rw [cast_ratPairing, cast_ratPairing]
  have h1 := scalarExtension_substitute M p
  have h2 := scalarExtension_substitute M.transpose q
  change factorialPairing (scalarExtensionPolynomial _) (scalarExtensionPolynomial _) =
    factorialPairing (scalarExtensionPolynomial _) (scalarExtensionPolynomial _)
  rw [h1, h2, realSubstitute_transpose_adjoint, Matrix.transpose_map]

/-- The rational Fischer pairing on degree-`n` homogeneous polynomials. -/
def ratInner (n : ℕ) : RationalCoefficients n →ₗ[ℚ] RationalCoefficients n →ₗ[ℚ] ℚ :=
  ratPairing.compl₁₂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ n).subtype
    (MvPolynomial.homogeneousSubmodule (Fin 3) ℚ n).subtype

theorem cast_ratInner (n : ℕ) (p q : RationalCoefficients n) :
    ((ratInner n p q : ℚ) : ℝ) = inner ℝ (scalarExtensionCoefficient n p) (scalarExtensionCoefficient n q) := by
  rw [coefficient_inner]
  exact cast_ratPairing p.val q.val

theorem scalarExtensionCoefficient_injective (n : ℕ) :
    Function.Injective (scalarExtensionCoefficient n) := by
  intro p q h
  apply Subtype.ext
  exact MvPolynomial.map_injective (algebraMap ℚ ℝ) (algebraMap ℚ ℝ).injective
    (congrArg Subtype.val h)

theorem ratInner_self_pos (n : ℕ) {p : RationalCoefficients n} (hp : p ≠ 0) : 0 < ratInner n p p := by
  have h : 0 < ((ratInner n p p : ℚ) : ℝ) := by
    rw [cast_ratInner]
    apply real_inner_self_pos.mpr
    intro h0
    apply hp
    apply scalarExtensionCoefficient_injective
    rw [h0]
    apply Subtype.ext
    simp [scalarExtensionCoefficient, scalarExtensionPolynomial]
  exact_mod_cast h


/-! ### The dual rational system is the contragredient -/

section Contragredient

open CategoryTheory TernaryPoly.SmoothSingularGlobal TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.IntegralGL3Congruence TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.CompactInteriorRelativeBoundary
open scoped TensorProduct

/-- The contragredient of the rational polynomial coefficients of the deck group. -/
abbrev contragredientDeckCoefficientRep (n : ℕ) : Rep.{0} ℚ DeckGroup :=
  Rep.of (rationalDeckCoefficientRep n 0).ρ.dual

instance contragredientDeckCoefficientRep_finiteDimensional (n : ℕ) :
    FiniteDimensional ℚ (contragredientDeckCoefficientRep n) :=
  inferInstanceAs (FiniteDimensional ℚ (Module.Dual ℚ (RationalCoefficients n)))

/-- The Fischer map `p ↦ ⟨p, ·⟩` from the rational polynomials to their dual. -/
def fischerDual (n : ℕ) : RationalCoefficients n →ₗ[ℚ] Module.Dual ℚ (RationalCoefficients n) :=
  ratInner n

theorem fischerDual_injective (n : ℕ) : Function.Injective (fischerDual n) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro p hp
  by_contra hne
  have := ratInner_self_pos n hne
  have h0 : ratInner n p p = 0 := by
    have := congrArg (fun f => f p) hp
    simpa [fischerDual] using this
  linarith

/-- **The rational Fischer pairing identifies `Sym^n` with its dual** (as `ℚ`-vector spaces). -/
def fischerEquiv (n : ℕ) : RationalCoefficients n ≃ₗ[ℚ] Module.Dual ℚ (RationalCoefficients n) :=
  LinearEquiv.ofBijective (fischerDual n)
    ⟨fischerDual_injective n, by
      rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      · exact fischerDual_injective n
      · exact (Subspace.dual_finrank_eq (K := ℚ) (V := RationalCoefficients n)).symm⟩

/-- The Fischer map intertwines the dual (`gᵀ`) action with the contragredient action. -/
theorem fischerEquiv_equivariant (n : ℕ) (g : DeckGroup) (p : RationalCoefficients n) :
    fischerEquiv n ((dualDeckCoefficientRep n).ρ g p) =
      (contragredientDeckCoefficientRep n).ρ g (fischerEquiv n p) := by
  apply LinearMap.ext
  intro q
  change ratPairing (TernaryPoly.PolynomialGLAction.substitute
      ((rationalDeckMatrix g : Matrix (Fin 3) (Fin 3) ℚ).transpose) p.val) q.val =
    ratPairing p.val ((rationalDeckCoefficientRep n 0).ρ g⁻¹ q).val
  rw [ratPairing_substitute]
  congr 1
  change _ = TernaryPoly.PolynomialGLAction.action 0 (rationalDeckMatrix g⁻¹) q.val
  rw [Matrix.transpose_transpose, TernaryPoly.PolynomialGLAction.action_apply]
  simp [TernaryPoly.PolynomialGLAction.determinantCharacter]

attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

local instance deckCoverFact' : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

/-- The real scalar extension of the contragredient is the real dual coefficient space. -/
def contraRealEquiv (n : ℕ) : realRep (contragredientDeckCoefficientRep n) ≃ₗ[ℝ] Coefficients n :=
  (LinearEquiv.baseChange ℚ ℝ _ _ (fischerEquiv n).symm).trans (coefficientScalarExtension n)

theorem contraRealEquiv_equivariant (n : ℕ) (g : DeckGroup)
    (z : realRep (contragredientDeckCoefficientRep n)) :
    contraRealEquiv n ((realRep (contragredientDeckCoefficientRep n)).ρ g z) =
      deckRep (Tdual n) g (contraRealEquiv n z) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro r φ
    have h := fischerEquiv_equivariant n g ((fischerEquiv n).symm φ)
    rw [LinearEquiv.apply_symm_apply] at h
    change coefficientScalarExtension n (r ⊗ₜ[ℚ] (fischerEquiv n).symm ((contragredientDeckCoefficientRep n).ρ g φ)) =
      deckRep (Tdual n) g (coefficientScalarExtension n (r ⊗ₜ[ℚ] (fischerEquiv n).symm φ))
    rw [← h, LinearEquiv.symm_apply_apply, coefficientScalarExtension_tmul, coefficientScalarExtension_tmul, map_smul,
      scalarExtension_dual_equivariant]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, map_add, map_add]

/-- **The genuine contragredient.**  The actual compact-to-ordinary map of the local system
`Hom_ℚ(Sym^n, ℚ)` (the contragredient of the polynomial coefficients) vanishes. -/
theorem contragredient_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (contragredientDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_of_equiv _ (deckRep (Tdual n)) (contraRealEquiv n)
    (fun g z => contraRealEquiv_equivariant n g z) (compactExact_dual hn)

/-- The complexified contragredient. -/
theorem complex_contragredient_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (doubleRep (contragredientDeckCoefficientRep n)) 2 = 0 :=
  compactForget_zero_double (contragredientDeckCoefficientRep n) (Tdual n) (Tcxd n)
    (fun g p => reImEquiv_complexRepresentation n (thetaHom g) p) (contraRealEquiv n)
    (fun g z => contraRealEquiv_equivariant n g z) (compactExact_complex_dual hn)

end Contragredient

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
