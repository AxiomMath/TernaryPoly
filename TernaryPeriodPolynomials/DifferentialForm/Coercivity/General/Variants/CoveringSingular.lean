module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringExactness
public import TernaryPeriodPolynomials.DifferentialForm.Coefficient.CompactForget

@[expose] public section


/-!
# The actual singular compact-to-ordinary map for the five coefficient systems

The global APIs of the original library (`SmoothSingularGlobalCompactForgetComparison`,
`SmoothSingularGlobalOriginalSmoothComparison`, `SmoothSingularGlobalCompactExactVanishing`) are
instantiated with the true coefficient and covering model: the fixed deck group
`DeckGroup = principalSixInK` acting on the symmetric space `Space`, the rational deck-group
representations `A : Rep ℚ DeckGroup`, and the genuine `CompactConvexCover` `compactConvexCover`.
`originalCompactForget_eq_zero_of_smooth_exact A C h` says: if `h : CompactExactInDegree (realRep A).ρ 1`
(every closed compactly supported smooth equivariant two-form with values in the real scalar
extension of `A` has a smooth equivariant primitive), then the actual singular
`compactForget singularCoveringProjection A 2` vanishes.  Here `h` is supplied from the Tier B
theorems of `Variants/CoveringExactness`, through the equivariant isomorphisms of the real scalar
extensions with the form-side coefficient spaces:

* real `Sym^n`: `rationalDeckCoefficientRep n e` (`real_compactForget_zero`);
* dual: `dualDeckCoefficientRep n`, polynomials in the basis vectors acted on by substitution of
  `gᵀ` (`dual_compactForget_zero`); its real scalar extension is the real dual coefficients
  `Tdual n`, the contragredient of `Sym^n` by the Fischer pairing (`inner_dualRep`);
* complex `Sym^n ℂ³`: the doubled rational system `V ⊕ V` (`complexDeckCoefficientRep`), the
  complex-forget of `ℂ = ℝ ⊕ iℝ` (`complex_compactForget_zero`).  This is a *model*: the library has
  no singular cohomology with `ℂ` coefficients.  The comparison with the complex local system, through
  the real-coefficient singular cohomology of the real forget of `Sym^n ℂ³`, is in
  `Variants/ComplexBaseChange` (`complex_realCompactForget_zero`, `complexDeckEquiv_J`);
* complexified dual (`complex_dual_compactForget_zero`);
* literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)`: the same rational model, whose real scalar
  extension is identified with `LitCoeff n` and the contragredient action by `litRealEquiv`
  (`lit_compactForget_zero`).

The interior-cover versions (`*_interior_compactForget_zero`) transfer the statements to the principal-six interior cover through `PolynomialFormPrincipalCover.principal_compactForget_zero`.

Two different duals occur and must be kept apart.  The *local real dual* is the real coefficient
system `Tdual n` (the Cartan twist of `Sym^n`), the real scalar extension of `dualDeckCoefficientRep n`
(`Sym^n(V)` with `g` acting by substitution of `gᵀ`); its identification with the real contragredient
is the Fischer pairing over `ℝ` (`DualDictionary.toDual_dualRep`).  The *`ℚ`-Fischer dictionary* is
the separate statement, proved in `Variants/RationalDual` (`fischerEquiv`,
`fischerEquiv_equivariant`), that `dualDeckCoefficientRep n` is `ℚ`-isomorphic as a `Rep` to the
genuine contragredient `Hom_ℚ(A, ℚ)` of `A = rationalDeckCoefficientRep n 0`.

All of this is for the fixed deck group / principal-six cover.  The general arithmetic-group statement
and the finite-cover / coefficient descent are in `Singular/*`, `Variants/SmoothInduction` and
`Variants/GeneralSingular`.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open CategoryTheory TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpacePositive (RealGL)
open TernaryPoly.CompactInteriorRelativeBoundary
open scoped TensorProduct

local instance deckCoverFact : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

section Rational

/-- Substitution by a rational matrix on rational homogeneous polynomials of degree `n`. -/
def dualSubst (n : ℕ) (M : Matrix (Fin 3) (Fin 3) ℚ) :
    RationalCoefficients n →ₗ[ℚ] RationalCoefficients n where
  toFun p := ⟨TernaryPoly.PolynomialGLAction.substitute M p.val,
    TernaryPoly.PolynomialGLAction.substitute_homogeneous M p.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

theorem dualSubst_val (n : ℕ) (M : Matrix (Fin 3) (Fin 3) ℚ) (p : RationalCoefficients n) :
    (dualSubst n M p).val = TernaryPoly.PolynomialGLAction.substitute M p.val := rfl

/-- The rational representation of `GL₃(ℤ)` on `Sym^n ℚ³`, polynomials in the basis vectors with `g`
acting by substitution of `gᵀ` (the Cartan-twisted, dual action on degree-`n` coefficients). -/
def integralDualAction (n : ℕ) :
    Representation ℚ (Matrix.GeneralLinearGroup (Fin 3) ℤ) (RationalCoefficients n) where
  toFun g := dualSubst n
    (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : TernaryPoly.PolynomialGLAction.GL3) :
      Matrix (Fin 3) (Fin 3) ℚ).transpose)
  map_one' := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp [dualSubst_val, TernaryPoly.PolynomialGLAction.substitute_one]
  map_mul' g h := by
    apply LinearMap.ext
    intro p
    apply Subtype.ext
    simp only [map_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.transpose_mul, dualSubst_val,
      Module.End.mul_apply]
    have := congrArg (fun q => q p.val)
      (TernaryPoly.PolynomialGLAction.substitute_comp
        (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) g : TernaryPoly.PolynomialGLAction.GL3) :
          Matrix (Fin 3) (Fin 3) ℚ).transpose)
        (((Matrix.GeneralLinearGroup.map (Int.castRingHom ℚ) h : TernaryPoly.PolynomialGLAction.GL3) :
          Matrix (Fin 3) (Fin 3) ℚ).transpose))
    exact this.symm


/-- The dual polynomial coefficients on the principal-six group. -/
abbrev polynomialDualCoefficients (n : ℕ) : Rep.{0} ℚ principalSix :=
  Rep.res principalSix.subtype (Rep.of (integralDualAction n))

/-- The dual polynomial coefficients on the fixed deck group. -/
abbrev dualDeckCoefficientRep (n : ℕ) : Rep.{0} ℚ DeckGroup :=
  Rep.res deckPrincipal (polynomialDualCoefficients n)

instance dualDeckCoefficientRep_finiteDimensional (n : ℕ) :
    FiniteDimensional ℚ (dualDeckCoefficientRep n) :=
  Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℚ n)

theorem dualDeckCoefficientRep_apply (n : ℕ) (g : DeckGroup) (p : RationalCoefficients n) :
    ((dualDeckCoefficientRep n).ρ g p : RationalCoefficients n).val =
      TernaryPoly.PolynomialGLAction.substitute ((rationalDeckMatrix g : Matrix (Fin 3) (Fin 3) ℚ).transpose)
        p.val := rfl

theorem scalarExtension_dual_equivariant (n : ℕ) (g : DeckGroup) (p : RationalCoefficients n) :
    scalarExtensionCoefficient n ((dualDeckCoefficientRep n).ρ g p) =
      deckRep (Tdual n) g (scalarExtensionCoefficient n p) := by
  apply Subtype.ext
  have h1 : (scalarExtensionCoefficient n ((dualDeckCoefficientRep n).ρ g p)).val =
      scalarExtensionPolynomial (TernaryPoly.PolynomialGLAction.substitute
        ((rationalDeckMatrix g : Matrix (Fin 3) (Fin 3) ℚ).transpose) p.val) := rfl
  have h2 : (deckRep (Tdual n) g (scalarExtensionCoefficient n p)).val =
      TernaryPoly.SL3PolynomialCoercivity.realSubstitute
        (((thetaHom (deckMatrix g))⁻¹ : RealGL) : TernaryPoly.SL3PolynomialCoercivity.Mat)
          (scalarExtensionPolynomial p.val) := rfl
  rw [h1, h2]
  rw [scalarExtension_substitute, thetaHom_inv_val]
  have hm : ((rationalDeckMatrix g : Matrix (Fin 3) (Fin 3) ℚ).transpose.map (algebraMap ℚ ℝ)) =
      ((deckMatrix g : RealGL) : TernaryPoly.SL3PolynomialCoercivity.Mat).transpose := by
    rw [Matrix.transpose_map]
    congr 1
  rw [hm]


end Rational

section RealDictionary

attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

theorem dual_scalarExtension_equivariant (n : ℕ) (g : DeckGroup)
    (z : ExtendedCoefficients n) :
    coefficientScalarExtension n ((dualDeckCoefficientRep n).ρ g |>.baseChange ℝ z) =
      deckRep (Tdual n) g (coefficientScalarExtension n z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    simp only [LinearMap.baseChange_tmul, coefficientScalarExtension_tmul, map_smul]
    exact congrArg (r • ·) (scalarExtension_dual_equivariant n g p)
  | add x y hx hy => simp only [map_add, hx, hy]


end RealDictionary

section Transport

variable (A : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ A]
attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

/-- Smooth exactness transports along an equivariant linear isomorphism of the real scalar
extension of rational coefficients with a finite dimensional real representation. -/
theorem compactExact_realRep_of_equiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (σ : Representation ℝ DeckGroup F) (e : realRep A ≃ₗ[ℝ] F)
    (he : ∀ g v, e ((realRep A).ρ g v) = σ g (e v)) (h : CompactExactInDegree σ 1) :
    CompactExactInDegree (realRep A).ρ 1 :=
  compactExact_coefficient_transport (realRep A).ρ σ e.toContinuousLinearEquiv he 1 h

/-- The actual compact-to-ordinary map of a rational deck-group system vanishes as soon as the
smooth covering complex of its real scalar extension is exact in the sense of `CompactExactInDegree`
for an equivariantly isomorphic finite dimensional real representation. -/
theorem compactForget_zero_of_equiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (σ : Representation ℝ DeckGroup F) (e : realRep A ≃ₗ[ℝ] F)
    (he : ∀ g v, e ((realRep A).ρ g v) = σ g (e v)) (h : CompactExactInDegree σ 1) :
    compactForget singularCoveringProjection A 2 = 0 :=
  originalCompactForget_eq_zero_of_smooth_exact A compactConvexCover
    (compactExact_realRep_of_equiv A σ e he h)

end Transport

section DualSingular

/-- **The actual compact-to-ordinary map vanishes for the dual coefficients** (fixed deck group). -/
theorem dual_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (dualDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_of_equiv (dualDeckCoefficientRep n) (deckRep (Tdual n))
    (coefficientScalarExtension n)
    (fun g v => dual_scalarExtension_equivariant n g v) (compactExact_dual hn)

end DualSingular



/-! ### Complex coefficients: the complex-forget dictionary -/

section Double

/-- The doubled rational representation `A ⊕ A`, with diagonal group action.
Its real scalar extension `(ℝ ⊗_ℚ A) × (ℝ ⊗_ℚ A)` models the underlying real representation of
`ℂ ⊗_ℚ A` through real and imaginary coordinates: `ℂ = ℝ ⊕ ℝ i` as a real vector space.
The rational identity is instead `ℚ(i) = ℚ ⊕ ℚ i`. This definition alone is not singular
cohomology with complex coefficients; the cohomology scalar-extension comparison
`H*(-; A) ⊗ ℂ ≅ H*(-; A ⊗ ℂ)` is not asserted here. -/
def doubleRep {G : Type} [Group G] (A : Rep.{0} ℚ G) : Rep.{0} ℚ G := Rep.of (A.ρ.prod A.ρ)

instance doubleRep_finiteDimensional {G : Type} [Group G] (A : Rep.{0} ℚ G) [FiniteDimensional ℚ A] :
    FiniteDimensional ℚ (doubleRep A) :=
  inferInstanceAs (FiniteDimensional ℚ (A × A))

/-- Real scalar extension commutes with doubling. -/
def realDoubleEquiv {G : Type} [Group G] (A : Rep.{0} ℚ G) :
    realRep (doubleRep A) ≃ₗ[ℝ] realRep A × realRep A :=
  TensorProduct.prodRight ℚ ℝ ℝ A A

theorem realDoubleEquiv_equivariant {G : Type} [Group G] (A : Rep.{0} ℚ G) (g : G)
    (z : realRep (doubleRep A)) :
    realDoubleEquiv A ((realRep (doubleRep A)).ρ g z) =
      ((realRep A).ρ g (realDoubleEquiv A z).1, (realRep A).ρ g (realDoubleEquiv A z).2) := by
  refine TensorProduct.inductionOn z ?_ ?_
  · intro r p
    rfl
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    rfl

end Double


section ComplexSingular

variable (V : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ V]

omit [FiniteDimensional ℚ V] in
/-- The real scalar extension of the doubled rational system is `Sym^n ℂ³` (real and imaginary
parts), given an identification `ε` of the real scalar extension of `V` with the real coefficients. -/
def doubleCxEquiv {n : ℕ} (ε : realRep V ≃ₗ[ℝ] Coefficients n) :
    realRep (doubleRep V) ≃ₗ[ℝ] ComplexCoefficients n :=
  ((realDoubleEquiv V).trans (ε.prodCongr ε)).trans (reImEquiv n).symm

omit [FiniteDimensional ℚ V] in
theorem doubleCxEquiv_equivariant {n : ℕ} (T : Representation ℝ RealGL (Coefficients n))
    (TC : Representation ℝ RealGL (ComplexCoefficients n))
    (hTC : ∀ g p, reImEquiv n (TC g p) = (T g (reImEquiv n p).1, T g (reImEquiv n p).2))
    (ε : realRep V ≃ₗ[ℝ] Coefficients n) (hε : ∀ g z, ε ((realRep V).ρ g z) = deckRep T g (ε z))
    (g : DeckGroup) (z : realRep (doubleRep V)) :
    doubleCxEquiv V ε ((realRep (doubleRep V)).ρ g z) = deckRep TC g (doubleCxEquiv V ε z) := by
  apply (reImEquiv n).injective
  have h1 := realDoubleEquiv_equivariant V g z
  simp only [doubleCxEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.prodCongr_apply]
  rw [h1]
  change (ε ((realRep V).ρ g (realDoubleEquiv V z).1), ε ((realRep V).ρ g (realDoubleEquiv V z).2)) =
    reImEquiv n (TC (deckMat g) ((reImEquiv n).symm (ε (realDoubleEquiv V z).1, ε (realDoubleEquiv V z).2)))
  rw [hTC]
  simp only [LinearEquiv.apply_symm_apply, hε]
  rfl

/-- **The complex-forget dictionary for singular cohomology.**  If `V` has real scalar extension
equivariantly isomorphic to the real representation `T` of coefficients `Sym^n`, and `TC` is a
complexification of `T` (`reImEquiv`), then the actual compact-to-ordinary map of the doubled
rational system `V ⊕ V` vanishes as soon as the covering complex for `TC` is smoothly exact. -/
theorem compactForget_zero_double {n : ℕ} (T : Representation ℝ RealGL (Coefficients n))
    (TC : Representation ℝ RealGL (ComplexCoefficients n))
    (hTC : ∀ g p, reImEquiv n (TC g p) = (T g (reImEquiv n p).1, T g (reImEquiv n p).2))
    (ε : realRep V ≃ₗ[ℝ] Coefficients n) (hε : ∀ g z, ε ((realRep V).ρ g z) = deckRep T g (ε z))
    (h : CompactExactInDegree (deckRep TC) 1) :
    compactForget singularCoveringProjection (doubleRep V) 2 = 0 :=
  compactForget_zero_of_equiv (doubleRep V) (deckRep TC) (doubleCxEquiv V ε)
    (doubleCxEquiv_equivariant V T TC hTC ε hε) h

end ComplexSingular


/-! ### The five coefficient systems and the actual singular compact-to-ordinary map -/

section Instances

/-- The complexification of the rational polynomial coefficients, as a rational system. -/
abbrev complexDeckCoefficientRep (n : ℕ) : Rep.{0} ℚ DeckGroup :=
  doubleRep (rationalDeckCoefficientRep n 0)

/-- The complexified dual coefficients, as a rational system. -/
abbrev complexDualDeckCoefficientRep (n : ℕ) : Rep.{0} ℚ DeckGroup :=
  doubleRep (dualDeckCoefficientRep n)

/-- **Real coefficients.**  The actual `H²_c → H²` map of the fixed-deck-group local system
`Sym^n` (any determinant twist `e`; the twist is trivial on the deck group) vanishes, with smooth
exactness proved by `Admissible.closed_compact_exact` (not the exactness theorem). -/
theorem real_compactForget_zero (n : ℕ) (hn : 0 < n) (e : ℤ) :
    compactForget singularCoveringProjection (rationalDeckCoefficientRep n e) 2 = 0 :=
  compactForget_zero_of_equiv _ (deckRep (Treal n)) (coefficientScalarExtension n)
    (fun g v => coefficientScalarExtension_equivariant n e g v) (compactExact_real hn)

/-- **Complex coefficients `Sym^n ℂ³`.** -/
theorem complex_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (complexDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_double (rationalDeckCoefficientRep n 0) (Treal n) (Tcx n)
    (fun g p => reImEquiv_complexRepresentation n g p) (coefficientScalarExtension n)
    (fun g z => coefficientScalarExtension_equivariant n 0 g z) (compactExact_complex hn)

/-- **Complexified dual coefficients.** -/
theorem complex_dual_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (complexDualDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_double (dualDeckCoefficientRep n) (Tdual n) (Tcxd n)
    (fun g p => reImEquiv_complexRepresentation n (thetaHom g) p)
    (coefficientScalarExtension n) (fun g z => dual_scalarExtension_equivariant n g z)
    (compactExact_complex_dual hn)

/-- The real scalar extension of the complexified dual system is the literal `ℂ`-linear dual
`StrongDual ℂ (Sym^n ℂ³)` (Fischer-Riesz identification `litPhi`), with the deck group acting by the
contragredient action `litRep`. -/
def litRealEquiv (n : ℕ) : realRep (complexDualDeckCoefficientRep n) ≃ₗ[ℝ] LitCoeff n :=
  (doubleCxEquiv (dualDeckCoefficientRep n) (coefficientScalarExtension n)).trans (litPhi n)

theorem litRealEquiv_equivariant (n : ℕ) (g : DeckGroup) (z : realRep (complexDualDeckCoefficientRep n)) :
    litRealEquiv n ((realRep (complexDualDeckCoefficientRep n)).ρ g z) =
      deckRep (Tlit n) g (litRealEquiv n z) := by
  have h := doubleCxEquiv_equivariant (dualDeckCoefficientRep n) (Tdual n) (Tcxd n)
    (fun g p => reImEquiv_complexRepresentation n (thetaHom g) p) (coefficientScalarExtension n)
    (fun g z => dual_scalarExtension_equivariant n g z) g z
  change litPhi n (doubleCxEquiv (dualDeckCoefficientRep n) (coefficientScalarExtension n)
    ((realRep (doubleRep (dualDeckCoefficientRep n))).ρ g z)) = litRep n (deckMat g) (litPhi n _)
  rw [h]
  exact litPhi_equivariant n (deckMat g) _

/-- **Literal dual coefficients `StrongDual ℂ (Sym^n ℂ³)`.**  The actual compact-to-ordinary map of
the rational model whose real scalar extension is the literal complex dual vanishes. -/
theorem lit_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (complexDualDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_of_equiv _ (deckRep (Tlit n)) (litRealEquiv n)
    (fun g z => litRealEquiv_equivariant n g z) (compactExact_lit hn)

end Instances


/-! ### Transfer to the principal-six interior cover -/

section Interior

open TernaryPoly.SymmetricSpaceBordifiedCohomology TernaryPoly.PolynomialFormPrincipalCover
  TernaryPoly.SymmetricSpaceAllTopBoundary

/-- **Real coefficients on the interior cover**: the gate `PositivePolynomialInnerVanishing`,
proved from the Tier B exactness `compactExact_real` instead of the exactness theorem. -/
theorem real_interior_compactForget_zero (n : ℕ) (hn : 0 < n) (e : ℤ) :
    compactForget interiorCover (polynomialCoefficients n e) 2 = 0 :=
  principal_compactForget_zero (polynomialCoefficients n e) (real_compactForget_zero n hn e)

/-- The positive-degree inner vanishing, with exactness from `Admissible.closed_compact_exact`. -/
theorem positivePolynomialInnerVanishing_of_tierB :
    PositivePolynomialInnerVanishing := fun n hn e => real_interior_compactForget_zero n hn e

/-- The dual polynomial coefficients on the interior cover. -/
theorem dual_interior_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget interiorCover (polynomialDualCoefficients n) 2 = 0 :=
  principal_compactForget_zero (polynomialDualCoefficients n) (dual_compactForget_zero n hn)

/-- The complexification `V ⊕ V` of the polynomial coefficients on the interior cover. -/
theorem complex_interior_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget interiorCover (doubleRep (polynomialCoefficients n 0)) 2 = 0 :=
  principal_compactForget_zero (doubleRep (polynomialCoefficients n 0)) (complex_compactForget_zero n hn)

/-- The complexified dual (and, by `litRealEquiv`, the literal complex dual) on the interior cover. -/
theorem complex_dual_interior_compactForget_zero (n : ℕ) (hn : 0 < n) :
    compactForget interiorCover (doubleRep (polynomialDualCoefficients n)) 2 = 0 :=
  principal_compactForget_zero (doubleRep (polynomialDualCoefficients n))
    (complex_dual_compactForget_zero n hn)

end Interior

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
