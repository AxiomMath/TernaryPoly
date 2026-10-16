module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.CoveringSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Intrinsic
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Singular.Orbit
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.OriginalSmoothComparison

@[expose] public section


/-!
# Complex coefficients: the complex-forget dictionary for singular cohomology

The paper's complex coefficient system is `E = Sym^n ℂ³`, the homogeneous polynomials of degree `n`
over `ℂ` with the substitution action of the deck group, and Proposition `ar:prop:coercivity` is about the
map `H²_c(X_Γ, E) → H²(X_Γ, E)`.  The library has no singular cohomology with `ℂ` coefficients, but it
has genuine singular cohomology with *real* coefficients: `TernaryPoly.SmoothSingularGlobal.
realCoverCompactForget A 2` is the compact-to-ordinary map for the real local system `realRep A =
ℝ ⊗_ℚ A`, defined from the real singular cochains `cochains DeckGroup (CoverOpen univ) (realRep A)` (this
is *not* the rational map tensored with `ℝ`, and its vanishing is obtained from smooth exactness
directly, without injectivity of rational classes).

A singular cochain with values in a complex vector space `E` is a function on singular simplices with
values in `E`, and the cochain complex of the local system `E` is the same set of functions whether `E` is
regarded over `ℂ` or over `ℝ`.  Hence the `ℂ`-linear map `H²_c(X, E) → H²(X, E)` is zero exactly when
its underlying `ℝ`-linear map is zero, and that map is the real-coefficient singular map for the real
representation `E|_ℝ`.  This file identifies `E|_ℝ` with the real scalar extension of the doubled rational
system `V ⊕ V` (the realification of `ℂ ⊗_ℚ V` is `ℝ ⊗_ℚ (V ⊕ V)`) by the canonical finite coefficientwise equivalence
`doubleCxEquiv` (real and imaginary coordinates), checks that the complex structure matches
(`doubleJ` corresponds to multiplication by `i`, `doubleCxEquiv_J`; the deck action is `ℂ`-linear,
`Tcx_comm_cxI`), and proves:

* `complex_realCompactForget_zero`, `complex_dual_realCompactForget_zero`, `lit_realCompactForget_zero`:
  the real-coefficient singular compact-to-ordinary map for the real forget of `Sym^n ℂ³`, of its
  complexified dual, and of the literal dual `StrongDual ℂ (Sym^n ℂ³)` vanishes (also `real_…`, `dual_…`).
  The input is the complex smooth exactness `compactExact_complex` etc. and the smooth/singular
  comparison `realCompactSmoothComparison_forget`.
* `compactForget_zero_of_real`: the rational map vanishes as soon as the real one does (injectivity of the
  rational classes into the real ones; this is the paper's "extension is faithful" step, used in
  the direction real ⟹ rational, after the complex/real statement has been proved directly).
* `compactForget_double_zero_iff`: the doubled rational model `V ⊕ V` has vanishing `compactForget` exactly
  when `V` does, so the complex-forget model neither gains nor loses information.

What is not claimed: the induced `ℂ`-vector space structure on the singular classes (through functoriality of
`realCoverCompactCohomology` in the coefficients) is not constructed; it is not needed, because a
`ℂ`-linear map vanishes iff its `ℝ`-forget does.  The statement is for the fixed deck group (the real
singular cohomology of the library exists only there).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open CategoryTheory CategoryTheory.Limits TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.SymmetricSpaceArithmeticProper TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpacePositive (RealGL)
open TernaryPoly.CompactInteriorRelativeBoundary
open scoped TensorProduct

local instance deckCoverFactBC : Fact (IsQuotientCoveringMap singularCoveringProjection DeckGroup) :=
  ⟨quotientProjection_quotientCovering⟩

/-! ### The complex structure on `Sym^n ℂ³` and on the doubled model -/

section ComplexStructure

/-- Multiplication by `i` on `Sym^n ℂ³` (real linear). -/
def cxI (n : ℕ) : ComplexCoefficients n →ₗ[ℝ] ComplexCoefficients n where
  toFun p := ⟨Complex.I • p.1, (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ n).smul_mem Complex.I p.2⟩
  map_add' p q := Subtype.ext (smul_add _ _ _)
  map_smul' r p := Subtype.ext (by
    change Complex.I • (r • p.1) = r • (Complex.I • p.1)
    exact smul_comm _ _ _)

theorem cxI_val (n : ℕ) (p : ComplexCoefficients n) : (cxI n p).1 = Complex.I • p.1 := rfl

/-- In real and imaginary coordinates multiplication by `i` is `(a, b) ↦ (-b, a)`. -/
theorem reImEquiv_cxI (n : ℕ) (p : ComplexCoefficients n) :
    reImEquiv n (cxI n p) = (-(reImEquiv n p).2, (reImEquiv n p).1) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · ext d
    change (rePoly (Complex.I • p.1)).coeff d = _
    simp [coeff_rePoly, coeff_imPoly, reImEquiv]
  · ext d
    change (imPoly (Complex.I • p.1)).coeff d = _
    simp [coeff_rePoly, coeff_imPoly, reImEquiv]

/-- The deck (indeed the whole `GL₃(ℝ)`) action on `Sym^n ℂ³` is `ℂ`-linear. -/
theorem Tcx_comm_cxI (n : ℕ) (g : RealGL) (p : ComplexCoefficients n) :
    complexRepresentation n g (cxI n p) = cxI n (complexRepresentation n g p) := by
  apply (reImEquiv n).injective
  rw [reImEquiv_complexRepresentation, reImEquiv_cxI, reImEquiv_cxI, reImEquiv_complexRepresentation]
  simp

/-- The complex structure `(a, b) ↦ (-b, a)` of the doubled rational model `V ⊕ V`. -/
def doubleJ {G : Type} [Group G] (V : Rep.{0} ℚ G) : doubleRep V →ₗ[ℚ] doubleRep V :=
  LinearMap.prod (-LinearMap.snd ℚ V V) (LinearMap.fst ℚ V V)

theorem doubleJ_apply {G : Type} [Group G] (V : Rep.{0} ℚ G) (a b : V) :
    doubleJ V ((a, b) : V × V) = ((-b, a) : V × V) := rfl

/-- The complex structure commutes with the group action: the doubled model is a `ℚ(i)`-representation. -/
theorem doubleJ_comm {G : Type} [Group G] (V : Rep.{0} ℚ G) (g : G) (a b : V) :
    doubleJ V ((doubleRep V).ρ g ((a, b) : V × V)) = (doubleRep V).ρ g (doubleJ V ((a, b) : V × V)) := by
  change ((-(V.ρ g b), V.ρ g a) : V × V) = (V.ρ g (-b), V.ρ g a)
  rw [map_neg]

theorem realDoubleEquiv_J {G : Type} [Group G] (V : Rep.{0} ℚ G) (z : realRep (doubleRep V)) :
    realDoubleEquiv V ((doubleJ V).baseChange ℝ z) =
      (-(realDoubleEquiv V z).2, (realDoubleEquiv V z).1) := by
  induction z using TensorProduct.inductionOn with
  | tmul r p =>
    rw [LinearMap.baseChange_tmul]
    obtain ⟨a, b⟩ := (p : V × V)
    change (r ⊗ₜ[ℚ] (-b), r ⊗ₜ[ℚ] a) = (-(r ⊗ₜ[ℚ] b), r ⊗ₜ[ℚ] a)
    rw [TensorProduct.tmul_neg]
  | add x y hx hy =>
    rw [map_add, map_add, hx, hy]
    simp only [map_add, Prod.fst_add, Prod.snd_add, neg_add]
    rfl

/-- The complex structure `J` of the doubled system corresponds to multiplication by `i` on `Sym^n ℂ³`
under the real/imaginary-coordinate dictionary `doubleCxEquiv`. -/
theorem doubleCxEquiv_J (V : Rep.{0} ℚ DeckGroup) {n : ℕ}
    (ε : realRep V ≃ₗ[ℝ] Coefficients n) (z : realRep (doubleRep V)) :
    doubleCxEquiv V ε ((doubleJ V).baseChange ℝ z) = cxI n (doubleCxEquiv V ε z) := by
  apply (reImEquiv n).injective
  rw [reImEquiv_cxI]
  simp only [doubleCxEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.prodCongr_apply]
  rw [realDoubleEquiv_J]
  simp

end ComplexStructure


/-! ### Real-coefficient singular compact-to-ordinary map -/

section RealSingular

variable (A : Rep.{0} ℚ DeckGroup) [FiniteDimensional ℚ A]
attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

/-- **Smooth exactness kills the real-coefficient singular compact-to-ordinary map**, through the actual
smooth/singular comparison `realCompactSmoothComparison_forget` (no rational classes involved). -/
theorem realCoverCompactForget_zero_of_exact (C : CompactConvexCover)
    (h : CompactExactInDegree (realRep A).ρ 1) : realCoverCompactForget A 2 = 0 := by
  have hz := compactInclusion_homology_two_eq_zero (realRep A).ρ h
  have hs := realCompactSmoothComparison_forget A C
  rw [hz, zero_comp] at hs
  exact (cancel_epi (realCompactSmoothComparison A C).hom).1 (hs.trans comp_zero.symm)

/-- The same, for any finite dimensional real representation `σ` equivariantly isomorphic to the real
scalar extension. -/
theorem realCoverCompactForget_zero_of_equiv {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (σ : Representation ℝ DeckGroup F) (e : realRep A ≃ₗ[ℝ] F)
    (he : ∀ g v, e ((realRep A).ρ g v) = σ g (e v)) (h : CompactExactInDegree σ 1) :
    realCoverCompactForget A 2 = 0 :=
  realCoverCompactForget_zero_of_exact A compactConvexCover (compactExact_realRep_of_equiv A σ e he h)

omit [FiniteDimensional ℚ A] in
/-- **Real ⟹ rational**: the rational compact-to-ordinary map vanishes as soon as the real-coefficient
map does, because rational ordinary classes inject into real ones. -/
theorem compactForget_zero_of_real (h : realCoverCompactForget A 2 = 0) :
    compactForget singularCoveringProjection A 2 = 0 := by
  have hs := originalRationalReal_compact_square A 2
  rw [h, Functor.map_zero, comp_zero] at hs
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply originalRationalRealOrdinary_injective A 2
  have hx := congrArg (fun f => f.hom x) hs
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply, map_zero] using hx

end RealSingular


/-! ### The five coefficient systems, real-coefficient singular maps -/

section Systems

attribute [local instance] realCoefficientNorm realCoefficientNormedSpace

/-- The real-coefficient singular map for the real polynomial system vanishes. -/
theorem real_realCompactForget_zero (n : ℕ) (hn : 0 < n) (e : ℤ) :
    realCoverCompactForget (rationalDeckCoefficientRep n e) 2 = 0 :=
  realCoverCompactForget_zero_of_equiv _ (deckRep (Treal n)) (coefficientScalarExtension n)
    (fun g v => coefficientScalarExtension_equivariant n e g v) (compactExact_real hn)

/-- The real-coefficient singular map for the dual polynomial system vanishes. -/
theorem dual_realCompactForget_zero (n : ℕ) (hn : 0 < n) :
    realCoverCompactForget (dualDeckCoefficientRep n) 2 = 0 :=
  realCoverCompactForget_zero_of_equiv _ (deckRep (Tdual n)) (coefficientScalarExtension n)
    (fun g v => dual_scalarExtension_equivariant n g v) (compactExact_dual hn)

/-- The canonical finite coefficientwise equivalence of the real scalar extension of the doubled model of
`Sym^n ℚ³` with `Sym^n ℂ³` (real and imaginary coordinates). -/
def complexDeckEquiv (n : ℕ) : realRep (complexDeckCoefficientRep n) ≃ₗ[ℝ] ComplexCoefficients n :=
  doubleCxEquiv (rationalDeckCoefficientRep n 0) (coefficientScalarExtension n)

/-- It intertwines the deck action on the real scalar extension with the complex-substitution action. -/
theorem complexDeckEquiv_equivariant (n : ℕ) (g : DeckGroup) (z : realRep (complexDeckCoefficientRep n)) :
    complexDeckEquiv n ((realRep (complexDeckCoefficientRep n)).ρ g z) =
      deckRep (Tcx n) g (complexDeckEquiv n z) :=
  doubleCxEquiv_equivariant (rationalDeckCoefficientRep n 0) (Treal n) (Tcx n)
    (fun g p => reImEquiv_complexRepresentation n g p) (coefficientScalarExtension n)
    (fun g z => coefficientScalarExtension_equivariant n 0 g z) g z

/-- It intertwines the complex structure `J` of the doubled model with multiplication by `i`. -/
theorem complexDeckEquiv_J (n : ℕ) (z : realRep (complexDeckCoefficientRep n)) :
    complexDeckEquiv n ((doubleJ (rationalDeckCoefficientRep n 0)).baseChange ℝ z) =
      cxI n (complexDeckEquiv n z) :=
  doubleCxEquiv_J (rationalDeckCoefficientRep n 0) (coefficientScalarExtension n) z

/-- **Complex coefficients `Sym^n ℂ³`.**  The real-coefficient singular compact-to-ordinary map of the real
forget of `Sym^n ℂ³` (equivalently, of the doubled rational system) vanishes. -/
theorem complex_realCompactForget_zero (n : ℕ) (hn : 0 < n) :
    realCoverCompactForget (complexDeckCoefficientRep n) 2 = 0 :=
  realCoverCompactForget_zero_of_equiv _ (deckRep (Tcx n)) (complexDeckEquiv n)
    (fun g z => complexDeckEquiv_equivariant n g z) (compactExact_complex hn)

/-- The canonical equivalence for the complexified dual system. -/
def complexDualDeckEquiv (n : ℕ) :
    realRep (complexDualDeckCoefficientRep n) ≃ₗ[ℝ] ComplexCoefficients n :=
  doubleCxEquiv (dualDeckCoefficientRep n) (coefficientScalarExtension n)

theorem complexDualDeckEquiv_equivariant (n : ℕ) (g : DeckGroup)
    (z : realRep (complexDualDeckCoefficientRep n)) :
    complexDualDeckEquiv n ((realRep (complexDualDeckCoefficientRep n)).ρ g z) =
      deckRep (Tcxd n) g (complexDualDeckEquiv n z) :=
  doubleCxEquiv_equivariant (dualDeckCoefficientRep n) (Tdual n) (Tcxd n)
    (fun g p => reImEquiv_complexRepresentation n (thetaHom g) p) (coefficientScalarExtension n)
    (fun g z => dual_scalarExtension_equivariant n g z) g z

theorem complexDualDeckEquiv_J (n : ℕ) (z : realRep (complexDualDeckCoefficientRep n)) :
    complexDualDeckEquiv n ((doubleJ (dualDeckCoefficientRep n)).baseChange ℝ z) =
      cxI n (complexDualDeckEquiv n z) :=
  doubleCxEquiv_J (dualDeckCoefficientRep n) (coefficientScalarExtension n) z

/-- **Complexified dual coefficients.** -/
theorem complex_dual_realCompactForget_zero (n : ℕ) (hn : 0 < n) :
    realCoverCompactForget (complexDualDeckCoefficientRep n) 2 = 0 :=
  realCoverCompactForget_zero_of_equiv _ (deckRep (Tcxd n)) (complexDualDeckEquiv n)
    (fun g z => complexDualDeckEquiv_equivariant n g z) (compactExact_complex_dual hn)

/-- **Literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)`** (contragredient action, via `litRealEquiv`). -/
theorem lit_realCompactForget_zero (n : ℕ) (hn : 0 < n) :
    realCoverCompactForget (complexDualDeckCoefficientRep n) 2 = 0 :=
  realCoverCompactForget_zero_of_equiv _ (deckRep (Tlit n)) (litRealEquiv n)
    (fun g z => litRealEquiv_equivariant n g z) (compactExact_lit hn)

/-- The rational doubled model of `Sym^n ℂ³` has vanishing `compactForget`, derived through the
real-coefficient map of the complex forget (`complex_realCompactForget_zero`), not from the rational
real-coefficient system alone. -/
theorem complex_compactForget_zero_of_real (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (complexDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_of_real _ (complex_realCompactForget_zero n hn)

/-- The same for the complexified dual (and, through `litRealEquiv`, the literal dual). -/
theorem complex_dual_compactForget_zero_of_real (n : ℕ) (hn : 0 < n) :
    compactForget singularCoveringProjection (complexDualDeckCoefficientRep n) 2 = 0 :=
  compactForget_zero_of_real _ (complex_dual_realCompactForget_zero n hn)

end Systems


/-! ### The doubled model neither gains nor loses information -/

section Additive

open TernaryPoly.EquivariantSingularCohomology TernaryPoly.FreeActionLinearization
  TernaryPoly.EquivariantSingularResolution

variable {G : Type} [Group G] {E : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (V : Rep.{0} ℚ G)

/-- Equivariant simplex functions into the doubled system are pairs of equivariant functions. -/
def pairFun {n : ℕ} (f₁ f₂ : equivariantFunctions G E V n) : equivariantFunctions G E (doubleRep V) n :=
  ⟨fun σ => ((f₁.val σ, f₂.val σ) : V × V), fun g σ => by
    have h₁ := f₁.property g σ
    have h₂ := f₂.property g σ
    change ((f₁.val (g • σ), f₂.val (g • σ)) : V × V) = (V.ρ g (f₁.val σ), V.ρ g (f₂.val σ))
    rw [h₁, h₂]⟩

/-- First component of an equivariant function into the doubled system. -/
def fstFun {n : ℕ} (f : equivariantFunctions G E (doubleRep V) n) : equivariantFunctions G E V n :=
  ⟨fun σ => (f.val σ : V × V).1, fun g σ => by
    have h := congrArg Prod.fst (f.property g σ)
    exact h⟩

/-- Second component of an equivariant function into the doubled system. -/
def sndFun {n : ℕ} (f : equivariantFunctions G E (doubleRep V) n) : equivariantFunctions G E V n :=
  ⟨fun σ => (f.val σ : V × V).2, fun g σ => by
    have h := congrArg Prod.snd (f.property g σ)
    exact h⟩

/-- Alternating sums in `V × V` are computed componentwise. -/
theorem alt_sum_prod_eq {k : ℕ} (s : Fin k → V × V) (x : V × V) :
    (∑ i : Fin k, (-1 : ℤ) ^ i.val • s i = x) ↔
      (∑ i : Fin k, (-1 : ℤ) ^ i.val • (s i).1 = x.1 ∧ ∑ i : Fin k, (-1 : ℤ) ^ i.val • (s i).2 = x.2) := by
  rw [Prod.ext_iff]
  simp [Prod.fst_sum, Prod.snd_sum]

theorem funVanish_double_iff (S : Set E) :
    FunVanish (G := G) (E := E) (doubleRep V) S ↔ FunVanish (G := G) (E := E) V S := by
  constructor
  · intro H f hf hv
    obtain ⟨g, hg⟩ := H (pairFun V f 0) (fun τ => by
      refine (alt_sum_prod_eq V (fun i => (pairFun V f 0).val ((TopCat.toSSet.obj E).δ i τ)) 0).mpr
        ⟨hf τ, ?_⟩
      simp [pairFun]) (fun σ hσ => by
      apply Prod.ext
      · exact hv σ hσ
      · rfl)
    refine ⟨fstFun V g, fun σ => ?_⟩
    exact ((alt_sum_prod_eq V (fun i => g.val ((TopCat.toSSet.obj E).δ i σ)) _).mp (hg σ).symm).1.symm
  · intro H f hf hv
    obtain ⟨g₁, hg₁⟩ := H (fstFun V f) (fun τ =>
      ((alt_sum_prod_eq V (fun i => f.val ((TopCat.toSSet.obj E).δ i τ)) 0).mp (hf τ)).1)
      (fun σ hσ => congrArg Prod.fst (hv σ hσ))
    obtain ⟨g₂, hg₂⟩ := H (sndFun V f) (fun τ =>
      ((alt_sum_prod_eq V (fun i => f.val ((TopCat.toSSet.obj E).δ i τ)) 0).mp (hf τ)).2)
      (fun σ hσ => congrArg Prod.snd (hv σ hσ))
    refine ⟨pairFun V g₁ g₂, fun σ => ?_⟩
    exact ((alt_sum_prod_eq V (fun i => (pairFun V g₁ g₂).val ((TopCat.toSSet.obj E).δ i σ))
      (f.val σ)).mpr ⟨(hg₁ σ).symm, (hg₂ σ).symm⟩).symm

end Additive

/-- **The doubled model `V ⊕ V` has vanishing `compactForget` exactly when `V` has** (fixed deck group). -/
theorem compactForget_double_zero_iff (V : Rep.{0} ℚ DeckGroup) :
    compactForget singularCoveringProjection (doubleRep V) 2 = 0 ↔
      compactForget singularCoveringProjection V 2 = 0 := by
  rw [compactForget_two_eq_zero_iff_funVanish, compactForget_two_eq_zero_iff_funVanish]
  exact forall_congr' fun K => funVanish_double_iff V _

/-- The same for every admissible group `Γ`: the doubled rational model neither gains nor loses
information. -/
theorem singularVanish_double_iff (Γ : Subgroup RealGL) (hΓ : Admissible Γ) (A : Rep.{0} ℚ Γ) :
    SingularVanish Γ hΓ (doubleRep A) ↔ SingularVanish Γ hΓ A := by
  let _ : Fact (IsQuotientCoveringMap (coverHom Γ) Γ) := ⟨hΓ.quotientCovering⟩
  unfold SingularVanish
  rw [compactForget_two_eq_zero_iff_funVanish, compactForget_two_eq_zero_iff_funVanish]
  exact forall_congr' fun K => funVanish_double_iff A _

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
