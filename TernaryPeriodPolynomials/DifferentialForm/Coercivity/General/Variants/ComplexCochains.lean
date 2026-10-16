module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexBaseChange

@[expose] public section


/-!
# Complex-valued equivariant singular cochains: transport of the compact closed-cochain primitive

`Variants/ComplexBaseChange` proves that the real-coefficient singular compact-to-ordinary map
`realCoverCompactForget A 2` vanishes for the real forget of `Sym^n ℂ³` and the other coefficient
systems.  Here the statement is made and proved at the level of the *actual complex-valued equivariant
singular cochains* of the covering `Space → X_Γ` (the deck group `DeckGroup`, the cover `CoverOpen univ`):

* a cochain is a function `f` on singular 2-simplices of `CoverOpen univ` with values in the complex vector
  space `Sym^n ℂ³` (`ComplexCoefficients n`), equivariant for the complex-substitution action of the deck
  group (`deckRep (Tcx n)`);
* it is closed when its alternating face sum over every singular 3-simplex vanishes;
* it has compact support `K` when it vanishes on every singular simplex of the open subspace
  `CoverOpen Kᶜ` (the kernel of the actual cochain restriction `coveringCochainRestriction`);
* the primitive is an equivariant function on 1-simplices whose alternating face sum is `f`.

`Variants/ComplexCochains.complex_cochain_primitive`: every closed equivariant complex cochain of compact
support has an equivariant primitive.  The proof transports `f` along the canonical coefficientwise
equivalence `complexDeckEquiv` (and its inverse) to a cochain with values in the real scalar extension of
the doubled rational system, shows that the transport commutes with the alternating-face differential,
with equivariance (`transportFun`, `transport_symm_equivariant`), with the differential
(`transportCochain_closed`, from the literal `cochainFunctionEquiv` and `evaluate_d` of the real cochain
model) and with the support condition (`transportCochain_support`, from the pullback formula
`evaluate_pullback`), applies the real
characterization `realCoverCompactForget_eq_zero_iff` of the actual real compact-to-ordinary map, and
transports the primitive back.  The same generic transport (`cochain_primitive_of_equiv`) gives the real,
dual, complexified-dual and literal-dual versions.

Formalized by Claude Sonnet 5.5.
-/

local notation "OSp" => TernaryPoly.SymmetricSpaceCovering.OrbitSpace

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open scoped Simplicial
open TopologicalSpace CategoryTheory CategoryTheory.Limits TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham
  TernaryPoly.SymmetricSpaceCovering TernaryPoly.PolynomialCoefficientMetric
  TernaryPoly.FreeActionLinearization HomologicalComplex

section Real

variable {G : Type} [Group G] {X Y : TopCat.{0}} [MulAction G X] [ContinuousConstSMul G X]
  [MulAction G Y] [ContinuousConstSMul G Y]

/-- **Pullback formula**: the actual cochain pullback along an equivariant map evaluates a pulled-back
function on a simplex as the original function on the image simplex. -/
theorem evaluate_pullback (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (V : Rep ℝ G)
    (n : ℕ) (φ : chainRep G Y n ⟶ V) (τ : SingularSimplex X n) :
    cochainFunctionEquiv G X V n ((cochainPullback f hf V).f n φ) τ =
      cochainFunctionEquiv G Y V n φ ((TopCat.toSSet.map f).app (Opposite.op ⦋n⦌) τ) := by
  have h := congrArg (fun u => u.hom 1)
    (SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f)
      (ModuleCat.of ℝ ℝ) τ)
  change φ.hom ((TernaryPoly.SmoothSingularComparison.realSingularChainMap f).f n
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) τ) 1)) = _
  exact congrArg (fun v => φ.hom v) h

end Real


section Compact

variable (A : Rep.{0} ℚ DeckGroup)

/-- **Intrinsic form of the vanishing of the real compact-to-ordinary map in degree two**: every closed
real equivariant cochain of the covering that restricts to zero on the open subspace `CoverOpen Kᶜ` of a
compact `K` is a coboundary. -/
theorem realCoverCompactForget_eq_zero_iff :
    realCoverCompactForget A 2 = 0 ↔ ∀ K : Compacts OSp,
      ∀ c : (coveringCochains (realRep A).ρ Set.univ).X 2,
        ((coveringCochains (realRep A).ρ Set.univ).d 2 3).hom c = 0 →
        ((coveringCochainRestriction (realRep A).ρ (Set.subset_univ (K : Set OSp)ᶜ)).f 2).hom c = 0 →
        ∃ y : (coveringCochains (realRep A).ρ Set.univ).X 1,
          ((coveringCochains (realRep A).ρ Set.univ).d 1 2).hom y = c := by
  constructor
  · intro h K c hd hr
    have h1 : homologyMap (kernel.ι (coveringCochainRestriction (realRep A).ρ
        (Set.subset_univ (K : Set OSp)ᶜ))) 2 = 0 := by
      have := colimit.ι_desc (realCoverForgetCocone A 2) K
      change colimit.ι (realCoverCompactDiagram A 2) K ≫ realCoverCompactForget A 2 = _ at this
      rw [h, comp_zero] at this
      exact this.symm
    exact (homologyMap_kernelι_eq_zero_iff _ 1).mp h1 c hr hd
  · intro h
    apply colimit.hom_ext
    intro K
    refine Eq.trans ?_ comp_zero.symm
    have := colimit.ι_desc (realCoverForgetCocone A 2) K
    change colimit.ι (realCoverCompactDiagram A 2) K ≫ realCoverCompactForget A 2 = _ at this
    rw [this]
    exact (homologyMap_kernelι_eq_zero_iff _ 1).mpr (fun c hr hd => h K c hd hr)

end Compact


section Transport

variable (A : Rep.{0} ℚ DeckGroup) {F : Type} [AddCommGroup F] [Module ℝ F]

/-- The covering space of the real singular model. -/
abbrev CovX : TopCat.{0} := TopCat.of (CoverOpen Set.univ)

/-- The simplices of the open subspace `CoverOpen Kᶜ` map into the simplices of the covering space. -/
abbrev inclSimplex (K : Compacts OSp) {n : ℕ}
    (τ : SingularSimplex (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) n) :
    GlobalCoverSimplex n :=
  (TopCat.toSSet.map (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ))).app (Opposite.op ⦋n⦌) τ

variable (σ : Representation ℝ DeckGroup F) (e : realRep A ≃ₗ[ℝ] F)
  (he : ∀ g v, e ((realRep A).ρ g v) = σ g (e v))

include he in
theorem transport_symm_equivariant (g : DeckGroup) (y : F) :
    e.symm (σ g y) = (realRep A).ρ g (e.symm y) := by
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- Transport of an `F`-valued equivariant simplex function to the real scalar extension. -/
def transportFun {n : ℕ} (f : GlobalCoverSimplex n → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex n), f (g • s) = σ g (f s)) :
    equivariantFunctions DeckGroup CovX (realRep A) n :=
  ⟨fun s => e.symm (f s), fun g s => by
    change e.symm (f (g • s)) = (realRep A).ρ g (e.symm (f s))
    rw [hequiv]
    exact transport_symm_equivariant A σ e he g _⟩

/-- The real cochain corresponding to an `F`-valued equivariant function. -/
def transportCochain {n : ℕ} (f : GlobalCoverSimplex n → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex n), f (g • s) = σ g (f s)) :
    (coveringCochains (realRep A).ρ Set.univ).X n :=
  (cochainFunctionEquiv DeckGroup CovX (realRep A) n).symm (transportFun A σ e he f hequiv)

theorem transportCochain_apply {n : ℕ} (f : GlobalCoverSimplex n → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex n), f (g • s) = σ g (f s))
    (s : GlobalCoverSimplex n) :
    cochainFunctionEquiv DeckGroup CovX (realRep A) n (transportCochain A σ e he f hequiv) s =
      e.symm (f s) := by
  have := (cochainFunctionEquiv DeckGroup CovX (realRep A) n).apply_symm_apply
    (transportFun A σ e he f hequiv)
  exact congrArg (fun u : equivariantFunctions DeckGroup CovX (realRep A) n => u.val s) this

theorem transportCochain_closed (f : GlobalCoverSimplex 2 → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex 2), f (g • s) = σ g (f s))
    (hclosed : ∀ τ : GlobalCoverSimplex 3,
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f ((TopCat.toSSet.obj CovX).δ i τ) = 0) :
    ((coveringCochains (realRep A).ρ Set.univ).d 2 3).hom (transportCochain A σ e he f hequiv) = 0 := by
  apply (cochainFunctionEquiv DeckGroup CovX (realRep A) 3).injective
  apply Subtype.ext
  funext τ
  have h1 := evaluate_d DeckGroup CovX (realRep A) 2 (transportCochain A σ e he f hequiv) τ
  refine h1.trans ?_
  have e1 : ∑ i : Fin 4, (-1 : ℤ) ^ i.val • cochainFunctionEquiv DeckGroup CovX (realRep A) 2
      (transportCochain A σ e he f hequiv) ((TopCat.toSSet.obj CovX).δ i τ) =
        e.symm (∑ i : Fin 4, (-1 : ℤ) ^ i.val • f ((TopCat.toSSet.obj CovX).δ i τ)) := by
    simp only [transportCochain_apply, map_sum, map_zsmul]
  rw [e1, hclosed τ, map_zero]
  exact (map_zero (cochainFunctionEquiv DeckGroup CovX (realRep A) 3)).symm ▸ rfl

theorem transportCochain_support (K : Compacts OSp) (f : GlobalCoverSimplex 2 → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex 2), f (g • s) = σ g (f s))
    (hsupp : ∀ τ : SingularSimplex (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) 2, f (inclSimplex K τ) = 0) :
    ((coveringCochainRestriction (realRep A).ρ (Set.subset_univ (K : Set OSp)ᶜ)).f 2).hom
      (transportCochain A σ e he f hequiv) = 0 := by
  apply (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) (realRep A) 2).injective
  apply Subtype.ext
  funext τ
  have h1 := evaluate_pullback (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ))
    (coverInclusion_equivariant (Set.subset_univ (K : Set OSp)ᶜ)) (realRep A) 2
    (transportCochain A σ e he f hequiv) τ
  refine h1.trans ?_
  rw [transportCochain_apply, hsupp τ, map_zero]
  exact (map_zero (cochainFunctionEquiv DeckGroup (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) (realRep A) 2)).symm ▸ rfl

include e he in
/-- **Generic transport of closed compact-support cochains.**  If the real compact-to-ordinary map of the
rational system `A` vanishes and `e : realRep A ≃ F` is an equivariant linear isomorphism onto the
representation `σ` on `F`, then every closed equivariant `F`-valued singular 2-cochain of the covering
that vanishes on all simplices of `CoverOpen Kᶜ` has an equivariant `F`-valued primitive. -/
theorem cochain_primitive_of_equiv (h : realCoverCompactForget A 2 = 0) (K : Compacts OSp)
    (f : GlobalCoverSimplex 2 → F)
    (hequiv : ∀ (g : DeckGroup) (s : GlobalCoverSimplex 2), f (g • s) = σ g (f s))
    (hclosed : ∀ τ : GlobalCoverSimplex 3,
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f ((TopCat.toSSet.obj CovX).δ i τ) = 0)
    (hsupp : ∀ τ : SingularSimplex (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) 2,
      f (inclSimplex K τ) = 0) :
    ∃ g : GlobalCoverSimplex 1 → F,
      (∀ (d : DeckGroup) (s : GlobalCoverSimplex 1), g (d • s) = σ d (g s)) ∧
        ∀ s : GlobalCoverSimplex 2, f s = ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
          g ((TopCat.toSSet.obj CovX).δ i s) := by
  obtain ⟨y, hy⟩ := (realCoverCompactForget_eq_zero_iff A).mp h K
    (transportCochain A σ e he f hequiv)
    (transportCochain_closed A σ e he f hequiv hclosed)
    (transportCochain_support A σ e he K f hequiv hsupp)
  refine ⟨fun s => e ((cochainFunctionEquiv DeckGroup CovX (realRep A) 1 y).val s), fun d s => ?_,
    fun s => ?_⟩
  · exact (congrArg e ((cochainFunctionEquiv DeckGroup CovX (realRep A) 1 y).property d s)).trans
      (he d _)
  · have h2 := evaluate_d DeckGroup CovX (realRep A) 1 y s
    have h3 : cochainFunctionEquiv DeckGroup CovX (realRep A) 2
        ((cochains DeckGroup CovX (realRep A)).d 1 2 y) s = e.symm (f s) := by
      rw [← transportCochain_apply A σ e he f hequiv s]
      exact congrArg (fun u => cochainFunctionEquiv DeckGroup CovX (realRep A) 2 u s) hy
    rw [h2] at h3
    have h4 := congrArg e h3
    rw [LinearEquiv.apply_symm_apply] at h4
    rw [← h4]
    simp only [map_sum, map_zsmul]

end Transport


section Systems

/-- **Closed compactly supported equivariant `F`-valued singular 2-cochains of the covering have an
equivariant primitive** (`F` with the deck action `σ`).  Cochains are functions on the singular simplices
of `CoverOpen univ`, closedness is the vanishing of the alternating face sum on 3-simplices, and compact
support `K` is vanishing on all simplices of `CoverOpen Kᶜ`. -/
def CochainPrimitive {F : Type} [AddCommGroup F] [Module ℝ F] (σ : Representation ℝ DeckGroup F) : Prop :=
  ∀ (K : Compacts OSp) (f : GlobalCoverSimplex 2 → F),
    (∀ (g : DeckGroup) (s : GlobalCoverSimplex 2), f (g • s) = σ g (f s)) →
    (∀ τ : GlobalCoverSimplex 3,
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f ((TopCat.toSSet.obj CovX).δ i τ) = 0) →
    (∀ τ : SingularSimplex (TopCat.of (CoverOpen (K : Set OSp)ᶜ)) 2, f (inclSimplex K τ) = 0) →
    ∃ g : GlobalCoverSimplex 1 → F,
      (∀ (d : DeckGroup) (s : GlobalCoverSimplex 1), g (d • s) = σ d (g s)) ∧
        ∀ s : GlobalCoverSimplex 2, f s = ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
          g ((TopCat.toSSet.obj CovX).δ i s)

/-- Real polynomial coefficients `Sym^n`, any determinant twist. -/
theorem real_cochain_primitive (n : ℕ) (hn : 0 < n) (e0 : ℤ) : CochainPrimitive (deckRep (Treal n)) :=
  fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv (rationalDeckCoefficientRep n e0) (deckRep (Treal n))
      (coefficientScalarExtension n) (fun g v => coefficientScalarExtension_equivariant n e0 g v)
      (real_realCompactForget_zero n hn e0) K f hequiv hclosed hsupp

/-- Dual coefficients. -/
theorem dual_cochain_primitive (n : ℕ) (hn : 0 < n) : CochainPrimitive (deckRep (Tdual n)) :=
  fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv (dualDeckCoefficientRep n) (deckRep (Tdual n))
      (coefficientScalarExtension n) (fun g v => dual_scalarExtension_equivariant n g v)
      (dual_realCompactForget_zero n hn) K f hequiv hclosed hsupp

/-- **Complex coefficients `Sym^n ℂ³`**: closed compactly supported complex-valued equivariant singular
2-cochains of the covering have an equivariant complex-valued primitive. -/
theorem complex_cochain_primitive (n : ℕ) (hn : 0 < n) : CochainPrimitive (deckRep (Tcx n)) :=
  fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv (complexDeckCoefficientRep n) (deckRep (Tcx n)) (complexDeckEquiv n)
      (fun g z => complexDeckEquiv_equivariant n g z)
      (complex_realCompactForget_zero n hn) K f hequiv hclosed hsupp

/-- Complexified dual coefficients. -/
theorem complex_dual_cochain_primitive (n : ℕ) (hn : 0 < n) : CochainPrimitive (deckRep (Tcxd n)) :=
  fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv (complexDualDeckCoefficientRep n) (deckRep (Tcxd n))
      (complexDualDeckEquiv n) (fun g z => complexDualDeckEquiv_equivariant n g z)
      (complex_dual_realCompactForget_zero n hn) K f hequiv hclosed hsupp

/-- Literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)` with the contragredient action. -/
theorem lit_cochain_primitive (n : ℕ) (hn : 0 < n) : CochainPrimitive (deckRep (Tlit n)) :=
  fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv (complexDualDeckCoefficientRep n) (deckRep (Tlit n)) (litRealEquiv n)
      (fun g z => litRealEquiv_equivariant n g z)
      (lit_realCompactForget_zero n hn) K f hequiv hclosed hsupp

end Systems

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
