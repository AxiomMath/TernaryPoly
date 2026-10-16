module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.HomologyZero
public import TernaryPeriodPolynomials.Analysis.Compact.Interior.RelativeBoundaryForget

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian

@[expose] public section


/-!
# Vanishing of the compact-to-ordinary map as a statement about equivariant simplex functions

`compactForget p V 2 = 0` for a quotient covering `p : E ⟶ B` with deck group `G` holds exactly when
for every compact `K ⊆ B` and every equivariant degree-two simplex function `f` on `E` with values in
`V` which is closed (`f ∘ ∂ = 0`) and vanishes on the simplices of `p⁻¹(Kᶜ)`, there is an
equivariant one-cochain `g` with `f = g ∘ ∂` (`compactForget_two_eq_zero_iff_funVanish`).  The proof
chains four equivalences: the colimit presentation of compact cohomology (a map out of the colimit
vanishes iff it does on every support), the kernel description of support cochains
(`homologyMap_kernelι_eq_zero_iff`), the Hom-cochain model `cochainIso` with the restriction square
`subordinateLocalIso_restriction`, and the identification of Hom cochains with equivariant simplex
functions (`cochainFunctionEquiv`).  This isolates the group-theoretic content of the vanishing, so
that restriction to a subgroup of finite index and induction can be treated with finite sums
(`Singular/Transfer`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex

noncomputable section
namespace TernaryPeriodPolynomials.Argument.GeneralCoercivity

open TernaryPoly.SmoothSingularGlobal

variable {R : Type} [Ring R]

theorem moduleHomologyMap_eq_zero_iff {S T : ShortComplex (ModuleCat.{0} R)} (f : S ⟶ T) :
    ShortComplex.homologyMap f = 0 ↔
      ∀ x : S.X₂, S.g.hom x = 0 → f.τ₂.hom x ∈ LinearMap.range T.f.hom := by
  constructor
  · intro h x hx
    have h1 := congrArg (fun φ => φ.hom (moduleClass S x hx)) h
    simp only [ModuleCat.hom_zero, LinearMap.zero_apply] at h1
    change ShortComplex.homologyMap f (moduleClass S x hx) = 0 at h1
    rw [moduleClass_natural, moduleClass_eq_zero_iff] at h1
    exact h1
  · exact moduleHomologyMap_eq_zero_of_boundaries f

/-- A cochain map of module complexes induces zero in degree `m + 1` homology exactly when every
cocycle is sent to a coboundary. -/
theorem cochainHomologyMap_eq_zero_iff {A B : CochainComplex (ModuleCat.{0} R) ℕ} (f : A ⟶ B)
    (m : ℕ) :
    homologyMap f (m + 1) = 0 ↔ ∀ x : A.X (m + 1), (A.d (m + 1) (m + 2)).hom x = 0 →
      ∃ y : B.X m, (B.d m (m + 1)).hom y = (f.f (m + 1)).hom x := by
  have hp : (ComplexShape.up ℕ).prev (m + 1) = m := by simp
  have hnx : (ComplexShape.up ℕ).next (m + 1) = m + 2 := by simp
  constructor
  · intro h x hx
    have h0 : ShortComplex.homologyMap ((shortComplexFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) (m + 1)).map f) = 0 := h
    have key := (moduleHomologyMap_eq_zero_iff _).mp h0 x (by
      change (A.d (m + 1) ((ComplexShape.up ℕ).next (m + 1))).hom x = 0
      rw [hnx]; exact hx)
    have key' : ∃ y : B.X ((ComplexShape.up ℕ).prev (m + 1)),
        (B.d ((ComplexShape.up ℕ).prev (m + 1)) (m + 1)).hom y = (f.f (m + 1)).hom x := key
    rw [hp] at key'
    exact key'
  · intro h
    exact cochainHomologyMap_eq_zero_of_boundaries f (m + 1) (fun x hx => by
      simpa using h x hx)


theorem range_kernelι_eq_ker {A B : CochainComplex (ModuleCat.{0} R) ℕ} (φ : A ⟶ B) (n : ℕ) :
    LinearMap.range ((kernel.ι φ).f n).hom = LinearMap.ker (φ.f n).hom := by
  have hex : (ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)).Exact := ShortComplex.exact_kernel φ
  have := (HomologicalComplex.exact_iff_degreewise_exact _).mp hex n
  exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp this

theorem kernelι_f_injective {A B : CochainComplex (ModuleCat.{0} R) ℕ} (φ : A ⟶ B) (n : ℕ) :
    Function.Injective ((kernel.ι φ).f n).hom := by
  have : Mono ((kernel.ι φ).f n) := inferInstance
  exact (ModuleCat.mono_iff_injective _).mp this

/-- Degree-`m + 1` cohomology of the kernel of a cochain map maps to zero in `A` exactly when every
cocycle of `A` killed by `φ` is a coboundary. -/
theorem homologyMap_kernelι_eq_zero_iff {A B : CochainComplex (ModuleCat.{0} R) ℕ} (φ : A ⟶ B)
    (m : ℕ) :
    homologyMap (kernel.ι φ) (m + 1) = 0 ↔ ∀ c : A.X (m + 1), (φ.f (m + 1)).hom c = 0 →
      (A.d (m + 1) (m + 2)).hom c = 0 → ∃ y : A.X m, (A.d m (m + 1)).hom y = c := by
  rw [cochainHomologyMap_eq_zero_iff]
  constructor
  · intro h c hφ hd
    have hc : c ∈ LinearMap.range ((kernel.ι φ).f (m + 1)).hom := by
      rw [range_kernelι_eq_ker]; exact hφ
    obtain ⟨x, rfl⟩ := hc
    have hx : ((kernel φ).d (m + 1) (m + 2)).hom x = 0 := by
      apply kernelι_f_injective φ (m + 2)
      have := congrArg (fun f => f.hom x) ((kernel.ι φ).comm (m + 1) (m + 2))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [← this, hd, map_zero]
    exact h x hx
  · intro h x hx
    have hφ : (φ.f (m + 1)).hom (((kernel.ι φ).f (m + 1)).hom x) = 0 := by
      have : ((kernel.ι φ).f (m + 1)).hom x ∈ LinearMap.ker (φ.f (m + 1)).hom := by
        rw [← range_kernelι_eq_ker]; exact ⟨x, rfl⟩
      exact this
    have hd : (A.d (m + 1) (m + 2)).hom (((kernel.ι φ).f (m + 1)).hom x) = 0 := by
      have := congrArg (fun f => f.hom x) ((kernel.ι φ).comm (m + 1) (m + 2))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
      rw [this, hx, map_zero]
    exact h _ hφ hd


section Intrinsic

open TopologicalSpace TernaryPoly.SingularLocalSupport TernaryPoly.SingularLocalCoefficient
  TernaryPoly.CompactInteriorRelativeBoundary TernaryPoly.EquivariantSingularSmall
  TernaryPoly.SingularCoverNaturality TernaryPoly.FreeActionLinearization
  TernaryPoly.EquivariantSingularResolution SphereOddDegree SphereOddDegree.AffineBarycentricSubdivision

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)

/-- **Intrinsic form of the vanishing of `compactForget` in degree two**: every ordinary cocycle that
restricts to zero off a compact set is a coboundary. -/
theorem compactForget_two_eq_zero_iff :
    compactForget p V 2 = 0 ↔ ∀ K : Compacts B, ∀ c : (localCochains p hp.out V).X 2,
      ((localCochains p hp.out V).d 2 3).hom c = 0 →
      ((localRestriction p (K : Set B)ᶜ V).f 2).hom c = 0 →
      ∃ y : (localCochains p hp.out V).X 1, ((localCochains p hp.out V).d 1 2).hom y = c := by
  constructor
  · intro h K c hd hr
    have h1 : homologyMap (supportInclusion p V (K : Set B)) 2 = 0 := by
      have := compactForget_classMap p V K 2
      rw [h, comp_zero] at this
      exact this.symm
    exact (homologyMap_kernelι_eq_zero_iff (localRestriction p (K : Set B)ᶜ V) 1).mp h1 c hr hd
  · intro h
    apply colimit.hom_ext
    intro K
    refine Eq.trans ?_ comp_zero.symm
    change compactClassMap p V K 2 ≫ compactForget p V 2 = 0
    rw [compactForget_classMap]
    exact (homologyMap_kernelι_eq_zero_iff (localRestriction p (K : Set B)ᶜ V) 1).mpr
      (fun c hr hd => h K c hd hr)


open TernaryPoly.EquivariantSingularCohomology in
/-- Intrinsic vanishing, translated from the geometric local cochains to Hom cochains of the
equivariant singular chains of the total space. -/
theorem localCond_iff_homCond (A : Set B) :
    (∀ c : (localCochains p hp.out V).X 2, ((localCochains p hp.out V).d 2 3).hom c = 0 →
      ((localRestriction p A V).f 2).hom c = 0 →
      ∃ y : (localCochains p hp.out V).X 1, ((localCochains p hp.out V).d 1 2).hom y = c) ↔
    (∀ f : (cochains G E V).X 2, ((cochains G E V).d 2 3).hom f = 0 →
      ((homPullback (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) V).f 2).hom f = 0 →
      ∃ g : (cochains G E V).X 1, ((cochains G E V).d 1 2).hom g = f) := by
  have hΦ := fun n => ConcreteCategory.bijective_of_isIso
    (((HomologicalComplex.eval _ _ n).mapIso (cochainIso p hp.out V)).hom)
  have hΨ := fun n => ConcreteCategory.bijective_of_isIso
    (((HomologicalComplex.eval _ _ n).mapIso (subordinateLocalIso p A V)).hom)
  have hsq := subordinateLocalIso_restriction p A V
  set Φ := cochainIso p hp.out V with hΦdef
  set Ψ := subordinateLocalIso p A V with hΨdef
  have hΦ2 : Function.Bijective (Φ.hom.f 2).hom := hΦ 2
  have hΦ1 : Function.Bijective (Φ.hom.f 1).hom := hΦ 1
  have hΨ2 : Function.Bijective (Ψ.hom.f 2).hom := hΨ 2
  have e2 : ∀ f : (cochains G E V).X 2,
      (Ψ.hom.f 2).hom (((homPullback (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) V).f 2).hom f) =
        ((localRestriction p A V).f 2).hom ((Φ.hom.f 2).hom f) := by
    intro f
    have := congrArg (fun F => (F.f 2).hom f) hsq
    simpa using this
  have d12 : ∀ g : (cochains G E V).X 1, (Φ.hom.f 2).hom (((cochains G E V).d 1 2).hom g) =
      ((localCochains p hp.out V).d 1 2).hom ((Φ.hom.f 1).hom g) := by
    intro g
    have := congrArg (fun F => F.hom g) (Φ.hom.comm 1 2)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
  have d23 : ∀ f : (cochains G E V).X 2, (Φ.hom.f 3).hom (((cochains G E V).d 2 3).hom f) =
      ((localCochains p hp.out V).d 2 3).hom ((Φ.hom.f 2).hom f) := by
    intro f
    have := congrArg (fun F => F.hom f) (Φ.hom.comm 2 3)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using this.symm
  have hΦ3 : Function.Injective (Φ.hom.f 3).hom := (hΦ 3).1
  constructor
  · intro H f hd hr
    obtain ⟨y, hy⟩ := H ((Φ.hom.f 2).hom f) (by
      rw [← d23, hd, map_zero]) (by rw [← e2, hr, map_zero])
    obtain ⟨g, rfl⟩ := hΦ1.2 y
    refine ⟨g, hΦ2.1 ?_⟩
    rw [d12, hy]
  · intro H c hd hr
    obtain ⟨f, rfl⟩ := hΦ2.2 c
    have hd' : ((cochains G E V).d 2 3).hom f = 0 := by
      apply hΦ3
      rw [d23, hd, map_zero]
    have hr' : ((homPullback (subordinateInclusion G E (p ⁻¹' A) (preimage_invariant p A)) V).f 2).hom f = 0 := by
      apply hΨ2.1
      rw [e2, hr, map_zero]
    obtain ⟨g, hg⟩ := H f hd' hr'
    exact ⟨(Φ.hom.f 1).hom g, by rw [← d12, hg]⟩


open TernaryPoly.EquivariantSingularCohomology in
theorem subordinate_pullback_eq_zero_iff (S : Set E) (hS : InvariantSet G E S) (n : ℕ)
    (f : chainRep G E n ⟶ V) :
    (subordinateInclusion G E S hS).f n ≫ f = 0 ↔
      ∀ σ : SingularSimplex E n, IsSubordinate S σ → cochainFunctionEquiv G E V n f σ = 0 := by
  constructor
  · intro h σ hσ
    have := congrArg (fun F : (subordinateComplex G E S hS).X n ⟶ V =>
      F.hom ⟨chainGenerator ℚ E n σ, Submodule.subset_span ⟨σ, hσ, rfl⟩⟩) h
    exact this
  · intro h
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    refine (predicateBasis E n (fun σ => IsSubordinate S σ)).ext (fun b => ?_)
    have hb := predicateBasis_apply E n (fun σ => IsSubordinate S σ) b
    have := h b.val b.property
    change f.hom (((subordinateInclusion G E S hS).f n).hom (predicateBasis E n (fun σ => IsSubordinate S σ) b)) = 0
    exact (congrArg f.hom hb).trans this


open TernaryPoly.EquivariantSingularCohomology in
/-- Degree-two primitive existence for closed equivariant simplex functions that vanish on the
simplices subordinate to `S`, the zero (exterior) region: for `compactForget` it is `S = p⁻¹(Kᶜ)`
with `K` compact. -/
def FunVanish (S : Set E) : Prop :=
  ∀ f : equivariantFunctions G E V 2,
    (∀ τ : SingularSimplex E 3,
      ∑ i : Fin 4, (-1 : ℤ) ^ i.val • f.val ((TopCat.toSSet.obj E).δ i τ) = 0) →
    (∀ σ : SingularSimplex E 2, IsSubordinate S σ → f.val σ = 0) →
    ∃ g : equivariantFunctions G E V 1, ∀ σ : SingularSimplex E 2,
      f.val σ = ∑ i : Fin 3, (-1 : ℤ) ^ i.val • g.val ((TopCat.toSSet.obj E).δ i σ)

open TernaryPoly.EquivariantSingularCohomology in
theorem homCond_iff_funVanish (S : Set E) (hS : InvariantSet G E S) :
    (∀ f : (cochains G E V).X 2, ((cochains G E V).d 2 3).hom f = 0 →
      ((homPullback (subordinateInclusion G E S hS) V).f 2).hom f = 0 →
      ∃ g : (cochains G E V).X 1, ((cochains G E V).d 1 2).hom g = f) ↔ FunVanish (G := G) (E := E) V S := by
  have hd2 : ∀ (f : (cochains G E V).X 2) (τ : SingularSimplex E 3),
      cochainFunctionEquiv G E V 3 (((cochains G E V).d 2 3).hom f) τ =
        ∑ i : Fin 4, (-1 : ℤ) ^ i.val • cochainFunctionEquiv G E V 2 f ((TopCat.toSSet.obj E).δ i τ) :=
    fun f τ => evaluate_d G E V 2 f τ
  have hd1 : ∀ (g : (cochains G E V).X 1) (σ : SingularSimplex E 2),
      cochainFunctionEquiv G E V 2 (((cochains G E V).d 1 2).hom g) σ =
        ∑ i : Fin 3, (-1 : ℤ) ^ i.val • cochainFunctionEquiv G E V 1 g ((TopCat.toSSet.obj E).δ i σ) :=
    fun g σ => evaluate_d G E V 1 g σ
  constructor
  · intro H f hf hv
    obtain ⟨g, hg⟩ := H ((cochainFunctionEquiv G E V 2).symm f) (by
      apply (cochainFunctionEquiv G E V 3).injective
      apply Subtype.ext
      funext τ
      refine (hd2 _ τ).trans ?_
      have := hf τ
      have z : cochainFunctionEquiv G E V 3 (0 : ↑((cochains G E V).X 3)) = 0 := map_zero _
      rw [z]
      simpa using this) (by
      change (subordinateInclusion G E S hS).f 2 ≫ ((cochainFunctionEquiv G E V 2).symm f) = 0
      rw [subordinate_pullback_eq_zero_iff]
      intro σ hσ
      simpa using hv σ hσ)
    refine ⟨cochainFunctionEquiv G E V 1 g, fun σ => ?_⟩
    have h1 := (hd1 g σ).symm.trans (congrArg (fun F => cochainFunctionEquiv G E V 2 F σ) hg)
    simpa using h1.symm
  · intro H f hf hv
    obtain ⟨g, hg⟩ := H (cochainFunctionEquiv G E V 2 f) (fun τ => by
      refine (hd2 f τ).symm.trans ?_
      have z := (congrArg (cochainFunctionEquiv G E V 3) hf).trans (map_zero _)
      exact congrArg (fun F : equivariantFunctions G E V 3 => F.val τ) z) (by
      intro σ hσ
      have : (subordinateInclusion G E S hS).f 2 ≫ f = 0 := hv
      exact (subordinate_pullback_eq_zero_iff (G := G) (E := E) V S hS 2 f).mp this σ hσ)
    refine ⟨(cochainFunctionEquiv G E V 1).symm g, ?_⟩
    apply (cochainFunctionEquiv G E V 2).injective
    apply Subtype.ext
    funext σ
    refine (hd1 _ σ).trans ?_
    simpa using (hg σ).symm


/-- **The actual compact-to-ordinary vanishing in degree two, as a statement about equivariant
simplex functions**: for every compact `K` of the base, each closed degree-two equivariant simplex
function vanishing on the simplices of `p⁻¹(Kᶜ)` is the coboundary of an equivariant one-cochain. -/
theorem compactForget_two_eq_zero_iff_funVanish :
    compactForget p V 2 = 0 ↔ ∀ K : Compacts B, FunVanish (G := G) (E := E) V (p ⁻¹' (K : Set B)ᶜ) := by
  rw [compactForget_two_eq_zero_iff]
  refine forall_congr' (fun K => ?_)
  rw [localCond_iff_homCond p V, homCond_iff_funVanish]

end Intrinsic

end TernaryPeriodPolynomials.Argument.GeneralCoercivity
