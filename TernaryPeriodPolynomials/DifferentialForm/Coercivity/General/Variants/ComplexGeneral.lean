module

public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.ComplexCochains
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.DescentSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.SmoothInduction
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Variants.GeneralSingular
public import TernaryPeriodPolynomials.DifferentialForm.Coercivity.General.Estimates.Descent

@[expose] public section


/-!
# Complex-valued singular `H²_c → H²` vanishing for every allowed arithmetic group

For a group `G` acting on `Space`, `EquivVanish G V` says that closed `G`-equivariant degree-two simplex
functions with values in the rational representation `V`, vanishing off `G · C` (`C` compact), are
coboundaries of equivariant one-cochains.  With `V = qRep σ`, the restriction of scalars of a real
representation `σ` on a real vector space `F` (for instance `Sym^n ℂ³` with the complex-substitution action),
this is the statement for **`F`-valued** (complex-valued) singular cochains, with no rational model.

* `equivVanish_deck_of_cochainPrimitive`: the complex-valued primitive of `Variants/ComplexCochains`
  (stated on `CoverOpen univ`) gives `EquivVanish` for the deck group on `Space`, by transport along the
  equivariant homeomorphism `coordinateCoverHomeomorph` (the transport commutes with faces, with the group
  action and with supports).
* `equivVanish_res_of_ind`: Shapiro in this model.
* `equivVanish_of_primitive`: for a finite-index admissible `H ≤ gamma0` with the primitive property of the
  real representation `T`, `EquivVanish H (qRep (T|_H))` (smooth Shapiro `compactExact_induced`, then
  `cochain_primitive_of_equiv`, then the transport, then Shapiro in the function model).
* `equivVanish_of_comm`, `equivVanish_{real,dual,complex,complex_dual,lit}_of_comm`: the transfer to every
  admissible `Γ` commensurable with `gamma0` (`Variants/GeneralSingular`).  No rational structure is needed: the
  complex system on `Γ` is `(Tcx n)|_Γ`.
* `equivVanish_{principal,conj,neat,neatConj,neatSL,gammaN}_*`: the allowed groups (principal congruence
  `Γ(N)`, `3 ∣ N`; rational conjugates; neat finite-index subgroups of `SL₃(ℤ)`; `Γ(N)`, `N ≥ 3`).
* `twRep`, `equivVanish_twisted_descent`, `equivVanish_paper_*`, `equivVanish_{K,kSL,GL}_*`: finite-group
  descent with the determinant twist `E_{n,t}` to the groups with torsion.

Formalized by Claude Sonnet 5.5.
-/

open scoped Simplicial
open TopologicalSpace CategoryTheory

local notation "OSp" => TernaryPoly.SymmetricSpaceCovering.OrbitSpace

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SymmetricSpacePositive TernaryPoly.SymmetricSpaceCovering
  TernaryPoly.FreeActionLinearization TernaryPoly.EquivariantSingularCohomology
  TernaryPoly.EquivariantSingularSmall

section Generic

variable {G : Type} [Group G] [MulAction G Space] [ContinuousConstSMul G Space]

/-- The `G`-saturation `G · C` of a subset of `Space`, for an abstract group acting on `Space`. -/
def satG (G : Type) [Group G] [MulAction G Space] (C : Set Space) : Set Space :=
  {x | ∃ g : G, ∃ c ∈ C, g • c = x}

/-- Equivariant compact-to-ordinary vanishing in degree two for an abstract group acting on `Space`. -/
def EquivVanish (V : Rep.{0} ℚ G) : Prop :=
  ∀ C : Set Space, IsCompact C → FunVanish (G := G) (E := TopCat.of Space) V (satG G C)ᶜ

theorem equivSingularVanish_eq (Γ : Subgroup RealGL) (V : Rep.{0} ℚ Γ) :
    EquivSingularVanish Γ V = EquivVanish V := rfl

end Generic

section Shapiro

variable {G H : Type} [Group G] [Group H] [MulAction G Space] [ContinuousConstSMul G Space]
  [MulAction H Space] [ContinuousConstSMul H Space] (φ : H →* G)
  (hact : ∀ (h : H) (x : Space), h • x = φ h • x)

include hact in
/-- **Shapiro in the equivariant function model.** -/
theorem equivVanish_res_of_ind (V : Rep.{0} ℚ G) (h : EquivVanish (indRep φ V)) :
    EquivVanish (Rep.res φ V) := by
  intro C hC
  refine funVanish_res_of_ind φ hact _ _ ?_ ?_ (h C hC)
  · intro g x hx hgx
    apply hx
    obtain ⟨g', c, hc, hg'⟩ := hgx
    exact ⟨g⁻¹ * g', c, hc, by rw [mul_smul, hg', inv_smul_smul]⟩
  · intro x hx hx'
    apply hx
    obtain ⟨k, c, hc, rfl⟩ := hx'
    exact ⟨φ k, c, hc, (hact k c).symm⟩

end Shapiro


section QRep

variable {G : Type} [Group G] {F : Type} [AddCommGroup F] [Module ℝ F] [Module ℚ F] [IsScalarTower ℚ ℝ F]

/-- Restriction of scalars of a real representation to `ℚ`. -/
def qRepresentation (σ : Representation ℝ G F) : Representation ℚ G F where
  toFun g := (σ g).restrictScalars ℚ
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    simp

/-- The rational representation underlying a real one. -/
abbrev qRep (σ : Representation ℝ G F) : Rep.{0} ℚ G := Rep.of (qRepresentation σ)

theorem qRep_apply (σ : Representation ℝ G F) (g : G) (v : F) : (qRep σ).ρ g v = σ g v := rfl

end QRep


section Transport

variable {G : Type} [Group G] {X Y : TopCat.{0}} [MulAction G X] [ContinuousConstSMul G X]
  [MulAction G Y] [ContinuousConstSMul G Y]

/-- Simplices are transported along an equivariant continuous map. -/
abbrev simpMap (f : X ⟶ Y) (n : ℕ) : SingularSimplex X n → SingularSimplex Y n :=
  (TopCat.toSSet.map f).app (Opposite.op ⦋n⦌)

theorem simpMap_smul (f : X ⟶ Y) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x) (n : ℕ) (g : G)
    (s : SingularSimplex X n) : simpMap f n (g • s) = g • simpMap f n s := by
  rw [singular_smul_eq_map G X, singular_smul_eq_map G Y]
  have h : scalarMap G X g ≫ f = f ≫ scalarMap G Y g := by
    ext x
    exact hf g x
  have := congrArg (fun k => (TopCat.toSSet.map k).app (Opposite.op ⦋n⦌) s) h
  simpa [Functor.map_comp] using this

theorem simpMap_face (f : X ⟶ Y) {n : ℕ} (i : Fin (n + 2)) (s : SingularSimplex X (n + 1)) :
    (TopCat.toSSet.obj Y).δ i (simpMap f (n + 1) s) = simpMap f n ((TopCat.toSSet.obj X).δ i s) :=
  (congrFun (congrArg (fun f => f.hom) ((TopCat.toSSet.map f).naturality (SimplexCategory.δ i).op)).symm s)

theorem simpMap_comp (f : X ⟶ Y) (g : Y ⟶ X) (hfg : f ≫ g = 𝟙 X) (n : ℕ) (s : SingularSimplex X n) :
    simpMap g n (simpMap f n s) = s := by
  have := congrArg (fun k => (TopCat.toSSet.map k).app (Opposite.op ⦋n⦌) s) hfg
  simpa [Functor.map_comp] using this

end Transport


section Bridge

open TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham

variable {F : Type} [AddCommGroup F] [Module ℝ F] [Module ℚ F] [IsScalarTower ℚ ℝ F]

/-- The coordinate homeomorphism `CoverOpen univ ≃ Space` as a morphism of spaces. -/
def hMap : CovX ⟶ TopCat.of Space :=
  TopCat.ofHom ⟨coordinateCoverHomeomorph, coordinateCoverHomeomorph.continuous⟩

/-- Its inverse. -/
def hInv : TopCat.of Space ⟶ CovX :=
  TopCat.ofHom ⟨coordinateCoverHomeomorph.symm, coordinateCoverHomeomorph.symm.continuous⟩

theorem hMap_equivariant (g : DeckGroup) (x : CovX) : hMap (g • x) = g • hMap x :=
  coordinateCoverHomeomorph_equivariant g x

theorem hInv_equivariant (g : DeckGroup) (y : TopCat.of Space) : hInv (g • y) = g • hInv y := by
  apply coordinateCoverHomeomorph.injective
  change coordinateCoverHomeomorph (coordinateCoverHomeomorph.symm (g • y)) =
    coordinateCoverHomeomorph (g • coordinateCoverHomeomorph.symm y)
  rw [coordinateCoverHomeomorph.apply_symm_apply, coordinateCoverHomeomorph_equivariant,
    coordinateCoverHomeomorph.apply_symm_apply]

theorem hInv_hMap : hInv ≫ hMap = 𝟙 (TopCat.of Space) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro y
  exact coordinateCoverHomeomorph.apply_symm_apply y

theorem hMap_hInv : hMap ≫ hInv = 𝟙 CovX := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact coordinateCoverHomeomorph.symm_apply_apply x

/-- **The complex-valued primitive on `CoverOpen univ` gives `EquivVanish` for the deck group on
`Space`.**  Faces, the group action and supports are transported along `coordinateCoverHomeomorph`. -/
theorem equivVanish_deck_of_cochainPrimitive (σ : Representation ℝ DeckGroup F)
    (hσ : CochainPrimitive σ) : EquivVanish (G := DeckGroup) (qRep σ) := by
  intro C hC f hcl hvan
  let K : Compacts OSp := ⟨quotientProjection '' C, hC.image quotientProjection_covering.continuous⟩
  obtain ⟨g1, hg1eq, hg1⟩ := hσ K (fun s => f.val (simpMap hMap 2 s))
    (fun g s => by
      rw [simpMap_smul hMap hMap_equivariant]
      exact f.property g _)
    (fun τ => by
      have := hcl (simpMap hMap 3 τ)
      simpa only [simpMap_face] using this)
    (fun τ => by
      apply hvan
      intro p hp
      obtain ⟨y, rfl⟩ := hp
      intro hmem
      obtain ⟨g, c, hc, hgc⟩ := hmem
      have h1 : quotientProjection (g • c) = quotientProjection c :=
        quotientProjection_quotientCovering.map_smul g
      have h2 : quotientProjection (hMap (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ)
          ((TopCat.toSSetObjEquiv _ _ τ) y))) ∈ (K : Set OSp)ᶜ := by
        have e : quotientProjection (hMap (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ)
            ((TopCat.toSSetObjEquiv _ _ τ) y))) =
            coordinateProjection ((TopCat.toSSetObjEquiv _ _ τ) y).val :=
          coordinateCover_projection (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ)
            ((TopCat.toSSetObjEquiv _ _ τ) y))
        rw [e]
        exact ((TopCat.toSSetObjEquiv _ _ τ) y).property.2
      have hgc' : g • c = hMap (coverInclusion (Set.subset_univ (K : Set OSp)ᶜ)
          ((TopCat.toSSetObjEquiv _ _ τ) y)) := hgc
      apply h2
      rw [← hgc', h1]
      exact ⟨c, hc, rfl⟩)
  refine ⟨⟨fun s => g1 (simpMap hInv 1 s), fun g s => ?_⟩, fun s => ?_⟩
  · change g1 (simpMap hInv 1 (g • s)) = σ g (g1 (simpMap hInv 1 s))
    rw [simpMap_smul hInv hInv_equivariant]
    exact hg1eq g _
  · have h3 := hg1 (simpMap hInv 2 s)
    rw [simpMap_comp hInv hMap hInv_hMap] at h3
    refine h3.trans ?_
    simp only [simpMap_face]

end Bridge


section Induced

open TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Module ℚ F] [IsScalarTower ℚ ℝ F]
  (T : Representation ℝ RealGL F) {H : Subgroup RealGL} (hle : H ≤ gamma0)

omit [FiniteDimensional ℝ F] in
theorem res_qRep_deck :
    Rep.res (toDeck hle) (qRep (deckRep T)) = qRep (T.comp H.subtype) := by
  change Rep.of ((qRepresentation (deckRep T)).comp (toDeck hle)) = Rep.of (qRepresentation (T.comp H.subtype))
  congr 1
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  change T (deckMat (toDeck hle h)) v = T (h : RealGL) v
  rw [deckMat_toDeck]

include hle in
/-- **Complex-valued (`F`-valued) equivariant vanishing for a finite-index admissible subgroup of the
cover.**  Real vanishing for the induced rational system (smooth Shapiro, Tier B), the complex
cochain transport, the transport to `Space`, and Shapiro in the function model. -/
theorem equivVanish_of_primitive [Finite (gamma0 ⧸ H.subgroupOf gamma0)] (hH : Admissible H)
    (V : Rep.{0} ℚ FDeck) [FiniteDimensional ℚ V] (ε : realRep V ≃ₗ[ℝ] F)
    (hε : ∀ g z, ε ((realRep V).ρ g z) = deckRep T g (ε z)) (hP : PrimitiveProperty T H) :
    EquivVanish (G := H) (qRep (T.comp H.subtype)) := by
  have : Finite (FDeck ⧸ (toDeck hle).range) := finite_deck_quotient hle
  have : Fintype (FDeck ⧸ (toDeck hle).range) := Fintype.ofFinite _
  let A : Rep.{0} ℚ FDeck := indRep (toDeck hle) V
  have he := fun g z => funext fun q => indRealEquiv_equivariant (toDeck hle) V (deckRep T) ε hε g z q
  have hz : realCoverCompactForget A 2 = 0 :=
    realCoverCompactForget_zero_of_equiv A (indReal T hle) (indRealEquiv (toDeck hle) V ε) he
      (compactExact_induced hle hH hP)
  have hprim : CochainPrimitive (indReal T hle) := fun K f hequiv hclosed hsupp =>
    cochain_primitive_of_equiv A (indReal T hle) (indRealEquiv (toDeck hle) V ε) he hz K f hequiv hclosed hsupp
  have hdeck := equivVanish_deck_of_cochainPrimitive (indReal T hle) hprim
  have hind : indRep (toDeck hle) (qRep (deckRep T)) = qRep (indReal T hle) := by
    change Rep.of (indRepresentation (toDeck hle) (qRep (deckRep T))) = Rep.of (qRepresentation (indReal T hle))
    congr 1
  have h1 : EquivVanish (G := FDeck) (indRep (toDeck hle) (qRep (deckRep T))) := by
    rw [hind]
    exact hdeck
  have h2 := equivVanish_res_of_ind (toDeck hle) (fun x y => (toDeck_smul hle x y).symm) _ h1
  rw [res_qRep_deck] at h2
  exact h2

end Induced


section General

open TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Module ℚ F] [IsScalarTower ℚ ℝ F] (T : Representation ℝ RealGL F)
  (V : Rep.{0} ℚ FDeck) [FiniteDimensional ℚ V] (ε : realRep V ≃ₗ[ℝ] F)
  (hε : ∀ g z, ε ((realRep V).ρ g z) = deckRep T g (ε z))
  (hPrim : ∀ H : Subgroup RealGL, Admissible H → PrimitiveProperty T H)

omit [FiniteDimensional ℚ V] [FiniteDimensional ℝ F] in
theorem res_qRep_inclusion {Γ' Γ : Subgroup RealGL} (hle : Γ' ≤ Γ) :
    Rep.res (Subgroup.inclusion hle) (qRep (T.comp Γ.subtype)) = qRep (T.comp Γ'.subtype) := rfl

include hε hPrim in
/-- **`F`-valued (complex-valued) equivariant vanishing for every admissible group commensurable with the
cover.**  Finite-cover and coefficient descent, as for the rational statement, but in the
equivariant function model with values in the real vector space `F`. -/
theorem equivVanish_of_comm {Γ : Subgroup RealGL} (hΓ : Admissible Γ) (hc : Γ.Commensurable gamma0) :
    EquivVanish (G := Γ) (qRep (T.comp Γ.subtype)) := by
  have := finite_gamma0_inf hc
  have := finite_Γ_inf hc
  have hH : Admissible (Γ ⊓ gamma0) := hΓ.mono inf_le_left
  have h := equivVanish_of_primitive T (inf_le_right : Γ ⊓ gamma0 ≤ gamma0) hH V ε hε
    (hPrim _ hH)
  exact (equivSingularVanish_of_finiteIndex (inf_le_left : Γ ⊓ gamma0 ≤ Γ) (qRep (T.comp Γ.subtype)) h :
    EquivSingularVanish Γ (qRep (T.comp Γ.subtype)))

end General


/-- The rational module structure of the literal dual, by restriction of the real one. -/
instance litCoeffModuleRat (n : ℕ) : Module ℚ (LitCoeff n) := Module.compHom (LitCoeff n) (algebraMap ℚ ℝ)

instance litCoeff_isScalarTower (n : ℕ) : IsScalarTower ℚ ℝ (LitCoeff n) :=
  ⟨fun a b c => by
    change (a • b : ℝ) • c = (algebraMap ℚ ℝ a) • (b • c)
    rw [← mul_smul, ← Algebra.smul_def]⟩

section Systems

open TernaryPoly.SmoothSingularGlobal TernaryPoly.SmoothCoveringDeRham TernaryPoly.PolynomialCoefficientMetric

variable {Γ : Subgroup RealGL} (hΓ : Admissible Γ) (hc : Γ.Commensurable gamma0) {n : ℕ} (hn : 0 < n)

include hΓ hc hn in
/-- **Real polynomial coefficients, `ℝ`-valued cochains, every allowed `Γ`.** -/
theorem equivVanish_real_of_comm :
    EquivVanish (G := Γ) (qRep ((Treal n).comp Γ.subtype)) :=
  equivVanish_of_comm (Treal n) (rationalDeckCoefficientRep n 0) (coefficientScalarExtension n)
    (fun g v => coefficientScalarExtension_equivariant n 0 g v) (fun _ hH => primitive_real hH hn) hΓ hc

include hΓ hc hn in
/-- **Dual real coefficients.** -/
theorem equivVanish_dual_of_comm :
    EquivVanish (G := Γ) (qRep ((Tdual n).comp Γ.subtype)) :=
  equivVanish_of_comm (Tdual n) (dualDeckCoefficientRep n) (coefficientScalarExtension n)
    (fun g v => dual_scalarExtension_equivariant n g v) (fun _ hH => primitive_dual hH hn) hΓ hc

include hΓ hc hn in
/-- **Complex coefficients `Sym^n ℂ³`, `Sym^n ℂ³`-valued cochains, every allowed `Γ`.** -/
theorem equivVanish_complex_of_comm :
    EquivVanish (G := Γ) (qRep ((Tcx n).comp Γ.subtype)) :=
  equivVanish_of_comm (Tcx n) (complexDeckCoefficientRep n) (complexDeckEquiv n)
    (fun g z => complexDeckEquiv_equivariant n g z) (fun _ hH => primitive_complex hH hn) hΓ hc

include hΓ hc hn in
/-- **Complexified dual coefficients.** -/
theorem equivVanish_complex_dual_of_comm :
    EquivVanish (G := Γ) (qRep ((Tcxd n).comp Γ.subtype)) :=
  equivVanish_of_comm (Tcxd n) (complexDualDeckCoefficientRep n) (complexDualDeckEquiv n)
    (fun g z => complexDualDeckEquiv_equivariant n g z) (fun _ hH => primitive_complex_dual hH hn) hΓ hc

include hΓ hc hn in
/-- **Literal `ℂ`-linear dual `StrongDual ℂ (Sym^n ℂ³)`** with the contragredient action. -/
theorem equivVanish_lit_of_comm :
    EquivVanish (G := Γ) (qRep ((Tlit n).comp Γ.subtype)) :=
  equivVanish_of_comm (Tlit n) (complexDualDeckCoefficientRep n) (litRealEquiv n)
    (fun g z => litRealEquiv_equivariant n g z) (fun _ hH => primitive_lit hH hn) hΓ hc

end Systems


section Unfold

variable {G : Type} [Group G] [MulAction G Space] [ContinuousConstSMul G Space]
  {F : Type} [AddCommGroup F] [Module ℝ F] [Module ℚ F] [IsScalarTower ℚ ℝ F]

/-- **The explicit `F`-valued form of `EquivVanish (qRep σ)`**: every equivariant `F`-valued function on
singular 2-simplices of `Space` that is closed (zero alternating face sum on 3-simplices) and vanishes on
the simplices contained in the complement of `G · C` (`C` compact) is the coboundary
`f s = ∑ (-1)^i g (δ i s)` of an equivariant `F`-valued function `g` on 1-simplices. -/
theorem equivVanish_qRep_iff (σ : Representation ℝ G F) :
    EquivVanish (G := G) (qRep σ) ↔ ∀ C : Set Space, IsCompact C →
      ∀ f : SingularSimplex (TopCat.of Space) 2 → F,
        (∀ (g : G) (s : SingularSimplex (TopCat.of Space) 2), f (g • s) = σ g (f s)) →
        (∀ τ : SingularSimplex (TopCat.of Space) 3,
          ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f ((TopCat.toSSet.obj (TopCat.of Space)).δ i τ) = 0) →
        (∀ s : SingularSimplex (TopCat.of Space) 2,
          SphereOddDegree.IsSubordinate (satG G C)ᶜ s → f s = 0) →
        ∃ g1 : SingularSimplex (TopCat.of Space) 1 → F,
          (∀ (g : G) (s : SingularSimplex (TopCat.of Space) 1), g1 (g • s) = σ g (g1 s)) ∧
          ∀ s : SingularSimplex (TopCat.of Space) 2, f s = ∑ i : Fin 3, (-1 : ℤ) ^ i.val •
            g1 ((TopCat.toSSet.obj (TopCat.of Space)).δ i s) := by
  constructor
  · intro h C hC f hequiv hcl hvan
    obtain ⟨g1, hg1⟩ := h C hC ⟨f, hequiv⟩ hcl hvan
    exact ⟨g1.val, g1.property, hg1⟩
  · intro h C hC f hcl hvan
    obtain ⟨g1, hg1eq, hg1⟩ := h C hC f.val f.property hcl hvan
    exact ⟨⟨g1, hg1eq⟩, hg1⟩

end Unfold

/-! ### The allowed groups: principal congruence, neat finite-index, rational conjugates -/

section Families

open scoped MatrixGroups
open TernaryPoly.PolynomialGLAction (GL3)
open TernaryPoly.PolynomialCoefficientMetric TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.IntegralGL3Congruence

/-- **`Γ(N)`, `3 ∣ N`, system `complex`, `F`-valued cochains.** -/
theorem equivVanish_principal_complex {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := principalReal N) (qRep ((Tcx n).comp (principalReal N).subtype)) :=
  equivVanish_complex_of_comm (admissible_principalReal h3) (commensurable_principalReal N hN) hn

/-- **Rational conjugate of `Γ(N)`, system `complex`.** -/
theorem equivVanish_conj_complex {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) (g0 : GL3) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (principalReal N) (embQ g0))
      (qRep ((Tcx n).comp (conjSubgroup (principalReal N) (embQ g0)).subtype)) :=
  equivVanish_complex_of_comm ((admissible_principalReal h3).conj _)
    (commensurable_principalReal_conj g0 N hN) hn

/-- **Neat (torsion-free) finite-index subgroups of `SL₃(ℤ)`, system `complex`.** -/
theorem equivVanish_neat_complex (H : Subgroup IntegralGL) [H.FiniteIndex] (hdet : ∀ h ∈ H, h.val.det = 1)
    (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := H.map realIntegral) (qRep ((Tcx n).comp (H.map realIntegral).subtype)) :=
  equivVanish_complex_of_comm (admissible_map_realIntegral_of_torsionFree H hdet htf)
    (commensurable_map_realIntegral H) hn

/-- **Rational conjugates of neat finite-index subgroups, system `complex`.** -/
theorem equivVanish_neatConj_complex (H : Subgroup IntegralGL) [H.FiniteIndex]
    (hdet : ∀ h ∈ H, h.val.det = 1) (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) (g0 : GL3) {n : ℕ}
    (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (H.map realIntegral) (embQ g0))
      (qRep ((Tcx n).comp (conjSubgroup (H.map realIntegral) (embQ g0)).subtype)) :=
  equivVanish_complex_of_comm ((admissible_map_realIntegral_of_torsionFree H hdet htf).conj _)
    (commensurable_conj_map_realIntegral H g0) hn

/-- **`ConvergenceC4.IsNeat` subgroups of `SL₃(ℤ)` of finite index, system `complex`.** -/
theorem equivVanish_neatSL_complex (Γ : Subgroup SL(3, ℤ)) [Γ.FiniteIndex] (hΓ : ConvergenceC4.IsNeat Γ)
    {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup Γ).map realIntegral)
      (qRep ((Tcx n).comp ((toGLSubgroup Γ).map realIntegral).subtype)) :=
  haveI := finiteIndex_toGLSubgroup Γ
  equivVanish_neat_complex (toGLSubgroup Γ) (toGLSubgroup_det Γ) (isNeat_toGLSubgroup hΓ).torsionFree hn

/-- **`Γ(N)` for every `N ≥ 3` (neat), system `complex`.** -/
theorem equivVanish_gammaN_complex {N : ℕ} (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral)
      (qRep ((Tcx n).comp ((toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral).subtype)) :=
  haveI : NeZero N := ⟨by omega⟩
  haveI := finiteIndex_gammaN N
  equivVanish_neatSL_complex (ConvergenceC4.gammaN N) (ConvergenceC4.gammaN_isNeat hN) hn

/-- **`Γ(N)`, `3 ∣ N`, system `complex_dual`, `F`-valued cochains.** -/
theorem equivVanish_principal_complex_dual {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := principalReal N) (qRep ((Tcxd n).comp (principalReal N).subtype)) :=
  equivVanish_complex_dual_of_comm (admissible_principalReal h3) (commensurable_principalReal N hN) hn

/-- **Rational conjugate of `Γ(N)`, system `complex_dual`.** -/
theorem equivVanish_conj_complex_dual {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) (g0 : GL3) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (principalReal N) (embQ g0))
      (qRep ((Tcxd n).comp (conjSubgroup (principalReal N) (embQ g0)).subtype)) :=
  equivVanish_complex_dual_of_comm ((admissible_principalReal h3).conj _)
    (commensurable_principalReal_conj g0 N hN) hn

/-- **Neat (torsion-free) finite-index subgroups of `SL₃(ℤ)`, system `complex_dual`.** -/
theorem equivVanish_neat_complex_dual (H : Subgroup IntegralGL) [H.FiniteIndex] (hdet : ∀ h ∈ H, h.val.det = 1)
    (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := H.map realIntegral) (qRep ((Tcxd n).comp (H.map realIntegral).subtype)) :=
  equivVanish_complex_dual_of_comm (admissible_map_realIntegral_of_torsionFree H hdet htf)
    (commensurable_map_realIntegral H) hn

/-- **Rational conjugates of neat finite-index subgroups, system `complex_dual`.** -/
theorem equivVanish_neatConj_complex_dual (H : Subgroup IntegralGL) [H.FiniteIndex]
    (hdet : ∀ h ∈ H, h.val.det = 1) (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) (g0 : GL3) {n : ℕ}
    (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (H.map realIntegral) (embQ g0))
      (qRep ((Tcxd n).comp (conjSubgroup (H.map realIntegral) (embQ g0)).subtype)) :=
  equivVanish_complex_dual_of_comm ((admissible_map_realIntegral_of_torsionFree H hdet htf).conj _)
    (commensurable_conj_map_realIntegral H g0) hn

/-- **`ConvergenceC4.IsNeat` subgroups of `SL₃(ℤ)` of finite index, system `complex_dual`.** -/
theorem equivVanish_neatSL_complex_dual (Γ : Subgroup SL(3, ℤ)) [Γ.FiniteIndex] (hΓ : ConvergenceC4.IsNeat Γ)
    {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup Γ).map realIntegral)
      (qRep ((Tcxd n).comp ((toGLSubgroup Γ).map realIntegral).subtype)) :=
  haveI := finiteIndex_toGLSubgroup Γ
  equivVanish_neat_complex_dual (toGLSubgroup Γ) (toGLSubgroup_det Γ) (isNeat_toGLSubgroup hΓ).torsionFree hn

/-- **`Γ(N)` for every `N ≥ 3` (neat), system `complex_dual`.** -/
theorem equivVanish_gammaN_complex_dual {N : ℕ} (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral)
      (qRep ((Tcxd n).comp ((toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral).subtype)) :=
  haveI : NeZero N := ⟨by omega⟩
  haveI := finiteIndex_gammaN N
  equivVanish_neatSL_complex_dual (ConvergenceC4.gammaN N) (ConvergenceC4.gammaN_isNeat hN) hn

/-- **`Γ(N)`, `3 ∣ N`, system `lit`, `F`-valued cochains.** -/
theorem equivVanish_principal_lit {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := principalReal N) (qRep ((Tlit n).comp (principalReal N).subtype)) :=
  equivVanish_lit_of_comm (admissible_principalReal h3) (commensurable_principalReal N hN) hn

/-- **Rational conjugate of `Γ(N)`, system `lit`.** -/
theorem equivVanish_conj_lit {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) (g0 : GL3) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (principalReal N) (embQ g0))
      (qRep ((Tlit n).comp (conjSubgroup (principalReal N) (embQ g0)).subtype)) :=
  equivVanish_lit_of_comm ((admissible_principalReal h3).conj _)
    (commensurable_principalReal_conj g0 N hN) hn

/-- **Neat (torsion-free) finite-index subgroups of `SL₃(ℤ)`, system `lit`.** -/
theorem equivVanish_neat_lit (H : Subgroup IntegralGL) [H.FiniteIndex] (hdet : ∀ h ∈ H, h.val.det = 1)
    (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := H.map realIntegral) (qRep ((Tlit n).comp (H.map realIntegral).subtype)) :=
  equivVanish_lit_of_comm (admissible_map_realIntegral_of_torsionFree H hdet htf)
    (commensurable_map_realIntegral H) hn

/-- **Rational conjugates of neat finite-index subgroups, system `lit`.** -/
theorem equivVanish_neatConj_lit (H : Subgroup IntegralGL) [H.FiniteIndex]
    (hdet : ∀ h ∈ H, h.val.det = 1) (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) (g0 : GL3) {n : ℕ}
    (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (H.map realIntegral) (embQ g0))
      (qRep ((Tlit n).comp (conjSubgroup (H.map realIntegral) (embQ g0)).subtype)) :=
  equivVanish_lit_of_comm ((admissible_map_realIntegral_of_torsionFree H hdet htf).conj _)
    (commensurable_conj_map_realIntegral H g0) hn

/-- **`ConvergenceC4.IsNeat` subgroups of `SL₃(ℤ)` of finite index, system `lit`.** -/
theorem equivVanish_neatSL_lit (Γ : Subgroup SL(3, ℤ)) [Γ.FiniteIndex] (hΓ : ConvergenceC4.IsNeat Γ)
    {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup Γ).map realIntegral)
      (qRep ((Tlit n).comp ((toGLSubgroup Γ).map realIntegral).subtype)) :=
  haveI := finiteIndex_toGLSubgroup Γ
  equivVanish_neat_lit (toGLSubgroup Γ) (toGLSubgroup_det Γ) (isNeat_toGLSubgroup hΓ).torsionFree hn

/-- **`Γ(N)` for every `N ≥ 3` (neat), system `lit`.** -/
theorem equivVanish_gammaN_lit {N : ℕ} (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral)
      (qRep ((Tlit n).comp ((toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral).subtype)) :=
  haveI : NeZero N := ⟨by omega⟩
  haveI := finiteIndex_gammaN N
  equivVanish_neatSL_lit (ConvergenceC4.gammaN N) (ConvergenceC4.gammaN_isNeat hN) hn

/-- **`Γ(N)`, `3 ∣ N`, system `real`, `F`-valued cochains.** -/
theorem equivVanish_principal_real {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := principalReal N) (qRep ((Treal n).comp (principalReal N).subtype)) :=
  equivVanish_real_of_comm (admissible_principalReal h3) (commensurable_principalReal N hN) hn

/-- **Rational conjugate of `Γ(N)`, system `real`.** -/
theorem equivVanish_conj_real {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) (g0 : GL3) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (principalReal N) (embQ g0))
      (qRep ((Treal n).comp (conjSubgroup (principalReal N) (embQ g0)).subtype)) :=
  equivVanish_real_of_comm ((admissible_principalReal h3).conj _)
    (commensurable_principalReal_conj g0 N hN) hn

/-- **Neat (torsion-free) finite-index subgroups of `SL₃(ℤ)`, system `real`.** -/
theorem equivVanish_neat_real (H : Subgroup IntegralGL) [H.FiniteIndex] (hdet : ∀ h ∈ H, h.val.det = 1)
    (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := H.map realIntegral) (qRep ((Treal n).comp (H.map realIntegral).subtype)) :=
  equivVanish_real_of_comm (admissible_map_realIntegral_of_torsionFree H hdet htf)
    (commensurable_map_realIntegral H) hn

/-- **Rational conjugates of neat finite-index subgroups, system `real`.** -/
theorem equivVanish_neatConj_real (H : Subgroup IntegralGL) [H.FiniteIndex]
    (hdet : ∀ h ∈ H, h.val.det = 1) (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) (g0 : GL3) {n : ℕ}
    (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (H.map realIntegral) (embQ g0))
      (qRep ((Treal n).comp (conjSubgroup (H.map realIntegral) (embQ g0)).subtype)) :=
  equivVanish_real_of_comm ((admissible_map_realIntegral_of_torsionFree H hdet htf).conj _)
    (commensurable_conj_map_realIntegral H g0) hn

/-- **`ConvergenceC4.IsNeat` subgroups of `SL₃(ℤ)` of finite index, system `real`.** -/
theorem equivVanish_neatSL_real (Γ : Subgroup SL(3, ℤ)) [Γ.FiniteIndex] (hΓ : ConvergenceC4.IsNeat Γ)
    {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup Γ).map realIntegral)
      (qRep ((Treal n).comp ((toGLSubgroup Γ).map realIntegral).subtype)) :=
  haveI := finiteIndex_toGLSubgroup Γ
  equivVanish_neat_real (toGLSubgroup Γ) (toGLSubgroup_det Γ) (isNeat_toGLSubgroup hΓ).torsionFree hn

/-- **`Γ(N)` for every `N ≥ 3` (neat), system `real`.** -/
theorem equivVanish_gammaN_real {N : ℕ} (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral)
      (qRep ((Treal n).comp ((toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral).subtype)) :=
  haveI : NeZero N := ⟨by omega⟩
  haveI := finiteIndex_gammaN N
  equivVanish_neatSL_real (ConvergenceC4.gammaN N) (ConvergenceC4.gammaN_isNeat hN) hn

/-- **`Γ(N)`, `3 ∣ N`, system `dual`, `F`-valued cochains.** -/
theorem equivVanish_principal_dual {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := principalReal N) (qRep ((Tdual n).comp (principalReal N).subtype)) :=
  equivVanish_dual_of_comm (admissible_principalReal h3) (commensurable_principalReal N hN) hn

/-- **Rational conjugate of `Γ(N)`, system `dual`.** -/
theorem equivVanish_conj_dual {N : ℕ} (h3 : 3 ∣ N) (hN : 0 < N) (g0 : GL3) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (principalReal N) (embQ g0))
      (qRep ((Tdual n).comp (conjSubgroup (principalReal N) (embQ g0)).subtype)) :=
  equivVanish_dual_of_comm ((admissible_principalReal h3).conj _)
    (commensurable_principalReal_conj g0 N hN) hn

/-- **Neat (torsion-free) finite-index subgroups of `SL₃(ℤ)`, system `dual`.** -/
theorem equivVanish_neat_dual (H : Subgroup IntegralGL) [H.FiniteIndex] (hdet : ∀ h ∈ H, h.val.det = 1)
    (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := H.map realIntegral) (qRep ((Tdual n).comp (H.map realIntegral).subtype)) :=
  equivVanish_dual_of_comm (admissible_map_realIntegral_of_torsionFree H hdet htf)
    (commensurable_map_realIntegral H) hn

/-- **Rational conjugates of neat finite-index subgroups, system `dual`.** -/
theorem equivVanish_neatConj_dual (H : Subgroup IntegralGL) [H.FiniteIndex]
    (hdet : ∀ h ∈ H, h.val.det = 1) (htf : ∀ h ∈ H, IsOfFinOrder h → h = 1) (g0 : GL3) {n : ℕ}
    (hn : 0 < n) :
    EquivVanish (G := conjSubgroup (H.map realIntegral) (embQ g0))
      (qRep ((Tdual n).comp (conjSubgroup (H.map realIntegral) (embQ g0)).subtype)) :=
  equivVanish_dual_of_comm ((admissible_map_realIntegral_of_torsionFree H hdet htf).conj _)
    (commensurable_conj_map_realIntegral H g0) hn

/-- **`ConvergenceC4.IsNeat` subgroups of `SL₃(ℤ)` of finite index, system `dual`.** -/
theorem equivVanish_neatSL_dual (Γ : Subgroup SL(3, ℤ)) [Γ.FiniteIndex] (hΓ : ConvergenceC4.IsNeat Γ)
    {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup Γ).map realIntegral)
      (qRep ((Tdual n).comp ((toGLSubgroup Γ).map realIntegral).subtype)) :=
  haveI := finiteIndex_toGLSubgroup Γ
  equivVanish_neat_dual (toGLSubgroup Γ) (toGLSubgroup_det Γ) (isNeat_toGLSubgroup hΓ).torsionFree hn

/-- **`Γ(N)` for every `N ≥ 3` (neat), system `dual`.** -/
theorem equivVanish_gammaN_dual {N : ℕ} (hN : 3 ≤ N) {n : ℕ} (hn : 0 < n) :
    EquivVanish (G := (toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral)
      (qRep ((Tdual n).comp ((toGLSubgroup (ConvergenceC4.gammaN N)).map realIntegral).subtype)) :=
  haveI : NeZero N := ⟨by omega⟩
  haveI := finiteIndex_gammaN N
  equivVanish_neatSL_dual (ConvergenceC4.gammaN N) (ConvergenceC4.gammaN_isNeat hN) hn

end Families


/-! ### Finite-group descent with the determinant twist, `F`-valued -/

section TwistDescent

variable {F : Type} [AddCommGroup F] [Module ℝ F] [Module ℚ F] [IsScalarTower ℚ ℝ F]

/-- The determinant twist `g ↦ det(g)^{-e} · T(g)` of a real representation of `GL₃(ℝ)`: for `e = t` the
coefficient module `E_{n,t} = Sym^n ⊗ det^{-t}` of the paper. -/
def twRep (e : ℤ) (T : Representation ℝ RealGL F) : Representation ℝ RealGL F where
  toFun g := detChar e g • T g
  map_one' := by
    apply LinearMap.ext
    intro v
    simp [detChar_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    simp only [map_mul, LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    rw [mul_comm]

omit [Module ℚ F] [IsScalarTower ℚ ℝ F] in
theorem twRep_of_det_one (e : ℤ) (T : Representation ℝ RealGL F) {g : RealGL} (hg : g.val.det = 1)
    (v : F) : twRep e T g v = T g v := by
  change detChar e g • T g v = T g v
  rw [detChar_of_det_one e hg, one_smul]

/-- **Descent with the determinant twist.**  If `Γ' ≤ Γ` has finite index, is admissible (so has
determinant one) and the untwisted `F`-valued system vanishes on `Γ'`, then the system twisted by
`det^{-e}` vanishes on `Γ` (rational transfer/averaging). -/
theorem equivVanish_twisted_descent {Γ' Γ : Subgroup RealGL} (hle : Γ' ≤ Γ)
    [Finite (Γ ⧸ Γ'.subgroupOf Γ)] (hΓ' : Admissible Γ') (e : ℤ) (T : Representation ℝ RealGL F)
    (h : EquivVanish (G := Γ') (qRep (T.comp Γ'.subtype))) :
    EquivVanish (G := Γ) (qRep ((twRep e T).comp Γ.subtype)) := by
  have hres : Rep.res (Subgroup.inclusion hle) (qRep ((twRep e T).comp Γ.subtype)) =
      qRep (T.comp Γ'.subtype) := by
    change Rep.of ((qRepresentation ((twRep e T).comp Γ.subtype)).comp (Subgroup.inclusion hle)) =
      Rep.of (qRepresentation (T.comp Γ'.subtype))
    congr 1
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact twRep_of_det_one e T (hΓ'.det_one g.1 g.2) v
  exact equivSingularVanish_of_finiteIndex hle (qRep ((twRep e T).comp Γ.subtype)) (by rw [hres]; exact h)

end TwistDescent

/-! ### The groups of the paper with torsion and determinant twist: `K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)` -/

section PaperGroups

open TernaryPoly.PolynomialCoefficientMetric TernaryPoly.SymmetricSpaceArithmeticProper
  TernaryPoly.IntegralGL3Congruence

variable {H : Subgroup IntegralGL} (hH : neatCover ≤ H) {n : ℕ} (hn : 0 < n) (t : ℤ)

include hH hn in
/-- **Descent from the neat normal cover `Γ(6) ∩ SL₃(ℤ)` to any `H ⊇ Γ(6) ∩ SL₃(ℤ)` of `GL₃(ℤ)`
(`K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)`), system `complex`, `F`-valued cochains, determinant twist `t`.** -/
theorem equivVanish_paper_complex :
    EquivVanish (G := H.map realIntegral) (qRep ((twRep t (Tcx n)).comp (H.map realIntegral).subtype)) := by
  have := finite_quotient_map_realIntegral hH
  exact equivVanish_twisted_descent (Subgroup.map_mono (f := realIntegral) hH)
    (admissible_map_realIntegral_of_torsionFree neatCover (toGLSubgroup_det _)
      neatCover_isNeat.torsionFree) t (Tcx n)
    (equivVanish_neat_complex neatCover (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn)

include hH hn in
/-- **Descent from the neat normal cover `Γ(6) ∩ SL₃(ℤ)` to any `H ⊇ Γ(6) ∩ SL₃(ℤ)` of `GL₃(ℤ)`
(`K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)`), system `complex_dual`, `F`-valued cochains, determinant twist `t`.** -/
theorem equivVanish_paper_complex_dual :
    EquivVanish (G := H.map realIntegral) (qRep ((twRep t (Tcxd n)).comp (H.map realIntegral).subtype)) := by
  have := finite_quotient_map_realIntegral hH
  exact equivVanish_twisted_descent (Subgroup.map_mono (f := realIntegral) hH)
    (admissible_map_realIntegral_of_torsionFree neatCover (toGLSubgroup_det _)
      neatCover_isNeat.torsionFree) t (Tcxd n)
    (equivVanish_neat_complex_dual neatCover (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn)

include hH hn in
/-- **Descent from the neat normal cover `Γ(6) ∩ SL₃(ℤ)` to any `H ⊇ Γ(6) ∩ SL₃(ℤ)` of `GL₃(ℤ)`
(`K`, `K ∩ SL₃(ℤ)`, `GL₃(ℤ)`), system `lit`, `F`-valued cochains, determinant twist `t`.** -/
theorem equivVanish_paper_lit :
    EquivVanish (G := H.map realIntegral) (qRep ((twRep t (Tlit n)).comp (H.map realIntegral).subtype)) := by
  have := finite_quotient_map_realIntegral hH
  exact equivVanish_twisted_descent (Subgroup.map_mono (f := realIntegral) hH)
    (admissible_map_realIntegral_of_torsionFree neatCover (toGLSubgroup_det _)
      neatCover_isNeat.torsionFree) t (Tlit n)
    (equivVanish_neat_lit neatCover (toGLSubgroup_det _) neatCover_isNeat.torsionFree hn)

/-- Abbreviation for the groups of the paper. -/
abbrev paperK : Subgroup IntegralGL := TernaryPoly.ModThreeGoodAction.K

/-- **`K`**, system `complex`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_K_complex (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (paperK).map realIntegral)
      (qRep ((twRep t (Tcx n)).comp ((paperK).map realIntegral).subtype)) :=
  equivVanish_paper_complex neatCover_le_K hn t

/-- **`kSL`**, system `complex`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_kSL_complex (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (kSL).map realIntegral)
      (qRep ((twRep t (Tcx n)).comp ((kSL).map realIntegral).subtype)) :=
  equivVanish_paper_complex neatCover_le_kSL hn t

/-- **`GL`**, system `complex`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_GL_complex (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := ((⊤ : Subgroup IntegralGL)).map realIntegral)
      (qRep ((twRep t (Tcx n)).comp (((⊤ : Subgroup IntegralGL)).map realIntegral).subtype)) :=
  equivVanish_paper_complex le_top hn t

/-- **`K`**, system `complex_dual`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_K_complex_dual (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (paperK).map realIntegral)
      (qRep ((twRep t (Tcxd n)).comp ((paperK).map realIntegral).subtype)) :=
  equivVanish_paper_complex_dual neatCover_le_K hn t

/-- **`kSL`**, system `complex_dual`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_kSL_complex_dual (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (kSL).map realIntegral)
      (qRep ((twRep t (Tcxd n)).comp ((kSL).map realIntegral).subtype)) :=
  equivVanish_paper_complex_dual neatCover_le_kSL hn t

/-- **`GL`**, system `complex_dual`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_GL_complex_dual (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := ((⊤ : Subgroup IntegralGL)).map realIntegral)
      (qRep ((twRep t (Tcxd n)).comp (((⊤ : Subgroup IntegralGL)).map realIntegral).subtype)) :=
  equivVanish_paper_complex_dual le_top hn t

/-- **`K`**, system `lit`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_K_lit (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (paperK).map realIntegral)
      (qRep ((twRep t (Tlit n)).comp ((paperK).map realIntegral).subtype)) :=
  equivVanish_paper_lit neatCover_le_K hn t

/-- **`kSL`**, system `lit`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_kSL_lit (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := (kSL).map realIntegral)
      (qRep ((twRep t (Tlit n)).comp ((kSL).map realIntegral).subtype)) :=
  equivVanish_paper_lit neatCover_le_kSL hn t

/-- **`GL`**, system `lit`, `F`-valued cochains, determinant twist `t` (`E_{n,t} ⊗ ℂ`). -/
theorem equivVanish_GL_lit (n : ℕ) (hn : 0 < n) (t : ℤ) :
    EquivVanish (G := ((⊤ : Subgroup IntegralGL)).map realIntegral)
      (qRep ((twRep t (Tlit n)).comp (((⊤ : Subgroup IntegralGL)).map realIntegral).subtype)) :=
  equivVanish_paper_lit le_top hn t

end PaperGroups

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
