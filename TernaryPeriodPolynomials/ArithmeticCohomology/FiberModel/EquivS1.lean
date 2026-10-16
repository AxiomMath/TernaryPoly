module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Homology.Coinvariants
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent
public import TernaryPeriodPolynomials.GroupCohomology.Homology.LiftExact

@[expose] public section


/-!
# Equivariance of the singular-chain comparison under a larger group (P06(b)(i), upstairs part)

Let `G` act on a contractible space `E` (continuously), let `N ⊲ G` be a normal finite index subgroup
acting freely, and let `A : Rep ℚ G`.  The library's comparison
`groupCoinvariantHomologyIso N E (Res A) n : H_n(N, Res A) ≅ H_n((Sing(E) ⊗ A)_N)`
(`TernaryPoly.SingularLocalHomology`, the first step of the neat-level duality) intertwines

* Mathlib's conjugation action `c_g = groupHomology.map (conj g) (ρ g)` of `g ∈ G` on `H_n(N, Res A)`
  with
* the diagonal action of `g` on `(Sing(E) ⊗ A)_N` induced by `g` acting on `E` and on `A`
  (`groupCoinvariantHomologyIso_conj`).

The proof compares `groupHomologyIso` of the singular resolution with that of the bar resolution along a
`G`-equivariant chain map `bar(G) → Sing(E)` (`barToSingular`, a lift into an exact non-projective
complex, `GroupHomology.LiftExact`) and applies `NormalDescent.conj_comparison`.  Also
`groupCoinvariantHomologyIso_hom_eq_gen`: the library's comparison is Mathlib's `groupHomologyIso` for
the singular resolution.

This is the upstairs half; the descent to the quotient space and the cap
product and Mayer-Vietoris steps are not covered.

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.EquivariantSingularResolution TernaryPoly.SingularLocalHomology CategoryTheory
  CategoryTheory.MonoidalCategory TernaryPeriodPolynomials.Argument.GroupHomology

variable {G : Type} [Group G] (E : TopCat.{0}) [MulAction G E] [ContinuousConstSMul G E]
  (N : Subgroup G)

/-- The restricted action of a subgroup is continuous. -/
instance subgroupContinuousConstSMul : ContinuousConstSMul N E :=
  ⟨fun g => continuous_const_smul (g : G)⟩

-- restriction of the singular chain complex to a subgroup is the singular chain complex of the subgroup
example : ((Rep.resFunctor N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (equivariantChains G E) = equivariantChains N E := rfl

/-- The Rep-valued complex `A ⊗ Sing(E)`. -/
abbrev Ygeo (A : Rep.{0} ℚ G) : ChainComplex (Rep.{0} ℚ G) ℕ :=
  ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).obj (equivariantChains G E)

example (A : Rep.{0} ℚ G) : CxN N (Ygeo E A) = coinvariantChains N E (Rep.res N.subtype A) := rfl

/-- The singular chains of a contractible space with a `G`-action are an exact augmented complex of
`G`-representations (no freeness needed). -/
def exactAugSingular [ContractibleSpace E] : ExactAugmentation (Rep.trivial ℚ G ℚ) where
  complex := equivariantChains G E
  π := augmentation G E
  w := equivariantD_augmentation G E
  epi_π := augmentation_epi G E
  exact₀ := augmented_exact G E
  exact_succ n :=
    ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n) (by simp [ChainComplex.prev])
      (by simp)).1 (equivariantChains_exactAt G E (n + 1) (Nat.succ_ne_zero n))

/-- A `G`-equivariant chain map from the bar resolution of `G` to the singular chains of `E`,
compatible with the augmentations. -/
def barToSingular [ContractibleSpace E] :
    Rep.barComplex ℚ G ⟶ equivariantChains G E :=
  ExactAugmentation.lift (Rep.barResolution ℚ G) (exactAugSingular E) (𝟙 _)


section GenericH

variable {H : Type} [Group H] (X : TopCat.{0}) [MulAction H X] [ContinuousConstSMul H X]
  [ContractibleSpace X] [IsCancelSMul H X]

open scoped Classical in
theorem comparisonMap_eq_gen (V : Rep.{0} ℚ H) :
    comparisonMap H X V = (groupHomology.inhomogeneousChainsIso V).hom ≫
      (((Rep.coinvariantsTensor ℚ H).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ H ℚ)) (Rep.barResolution ℚ H)
          (projectiveResolution H X)) := rfl

open scoped Classical in
/-- The library's comparison isomorphism is Mathlib's `groupHomologyIso` for the singular resolution. -/
theorem groupCoinvariantHomologyIso_hom_eq_gen (V : Rep.{0} ℚ H) (n : ℕ) :
    (groupCoinvariantHomologyIso H X V n).hom =
      (_root_.groupHomologyIso V n (projectiveResolution H X)).hom := by
  have h := groupHomologyIso_hom_comp V n
    (ProjectiveResolution.lift (𝟙 _) (Rep.barResolution ℚ H) (projectiveResolution H X))
    (by
      have := ProjectiveResolution.lift_commutes_zero (𝟙 (Rep.trivial ℚ H ℚ))
        (Rep.barResolution ℚ H) (projectiveResolution H X)
      erw [Category.comp_id] at this
      exact this)
  rw [groupHomologyIso_bar_hom] at h
  refine Eq.trans ?_ h
  refine Eq.trans ?_ (HomologicalComplex.homologyMap_comp (groupHomology.inhomogeneousChainsIso V).hom
    ((((Rep.coinvariantsTensor ℚ H).obj V).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (ProjectiveResolution.lift (𝟙 (Rep.trivial ℚ H ℚ)) (Rep.barResolution ℚ H)
        (projectiveResolution H X))) n)
  exact congrArg (fun c => HomologicalComplex.homologyMap c n) (comparisonMap_eq_gen X V)

end GenericH

theorem GY_naturality {k : Type} [Field k] {K : Type} [Group K] (N : Subgroup K) [N.Normal]
    {Y Y' : ChainComplex (Rep.{0} k K) ℕ} (ψ : Y ⟶ Y') (g : K) :
    ((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map ψ ≫ GY N Y' g =
      GY N Y g ≫ ((cN (k := k) N).mapHomologicalComplex (ComplexShape.down ℕ)).map ψ :=
  HomologicalComplex.hom_ext _ _ fun i => (gamNat (k := k) N g).naturality (ψ.f i)

universe u in
theorem groupHomologyIso_inst_indep {k G : Type u} [CommRing k] [Group G] (i1 i2 : DecidableEq G)
    (A : Rep.{u} k G) (n : ℕ) (P : ProjectiveResolution (Rep.trivial k G k)) :
    @groupHomologyIso k G _ _ i1 A n P = @groupHomologyIso k G _ _ i2 A n P := by
  cases Subsingleton.elim i1 i2
  rfl

section Main

variable [ContractibleSpace E] [N.Normal] [N.FiniteIndex] [IsCancelSMul N E]

omit [N.Normal] [N.FiniteIndex] in
theorem barToSingular_res_comm :
    (((Rep.resFunctor N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (barToSingular E)).f 0 ≫ (projectiveResolution N E).π.f 0 =
      ((Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)).π.f 0 := by
  have h0 := ExactAugmentation.lift_f_zero_comp (Rep.barResolution ℚ G) (exactAugSingular E) (𝟙 _)
  erw [Category.comp_id] at h0
  have h := congrArg (Rep.resFunctor N.subtype).map h0
  rw [CategoryTheory.Functor.map_comp] at h
  exact h

end Main

section Upstairs

variable [ContractibleSpace E] [N.Normal] [N.FiniteIndex] [IsCancelSMul N E]

omit [N.FiniteIndex] in
/-- **(i), upstairs.**  The library's comparison `H_n(Γ, Res A) ≅ H_n((Sing(E) ⊗ A)_Γ)` for a group
`Γ = N` acting freely on a contractible space `E` carrying an action of a larger group `G`
intertwines Mathlib's conjugation action `c_g = H_n(conj g, ρ g)` with the diagonal action of `g ∈ G`
on `(Sing(E) ⊗ A)_N`. -/
theorem groupCoinvariantHomologyIso_conj (A : Rep.{0} ℚ G) (n : ℕ) (g : G) :
    groupHomology.map (conjN N g) (conjRep N A g) n ≫
        (groupCoinvariantHomologyIso N E (Rep.res N.subtype A) n).hom =
      (groupCoinvariantHomologyIso N E (Rep.res N.subtype A) n).hom ≫
        HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n := by
  classical
  let ι2 : DecidableEq ↥N := fun a b => Classical.propDecidable (a = b)
  let P := (Rep.resFunctor N.subtype).mapProjectiveResolution (Rep.barResolution ℚ G)
  let Q := projectiveResolution N E
  let ψY : YA A ⟶ Ygeo E A :=
    ((tensorLeft A).mapHomologicalComplex (ComplexShape.down ℕ)).map (barToSingular E)
  let Fφ : CxN N (YA A) ⟶ CxN N (Ygeo E A) :=
    ((cN (k := ℚ) N).mapHomologicalComplex (ComplexShape.down ℕ)).map ψY
  have h0 : (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
      HomologicalComplex.homologyMap Fφ n =
      (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n Q).hom :=
    @groupHomologyIso_hom_comp ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P Q
      (((Rep.resFunctor N.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (barToSingular E)) (barToSingular_res_comm (E := E) N)
  have h1 := groupCoinvariantHomologyIso_hom_eq_gen (H := ↥N) E (Rep.res N.subtype A) n
  have h2 := conj_comparison N A g n
  have h3 : eN N A n = @groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P :=
    groupHomologyIso_inst_indep _ _ _ _ _
  have h4 : HomologicalComplex.homologyMap (GY N (YA A) g) n ≫ HomologicalComplex.homologyMap Fφ n =
      HomologicalComplex.homologyMap Fφ n ≫ HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← GY_naturality N ψY g]
  rw [h1]
  rw [h3] at h2
  calc _ = groupHomology.map (conjN N g) (conjRep N A g) n ≫
        ((@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
          HomologicalComplex.homologyMap Fφ n) :=
      congrArg (fun z => groupHomology.map (conjN N g) (conjRep N A g) n ≫ z) h0.symm
    _ = (groupHomology.map (conjN N g) (conjRep N A g) n ≫
        (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom) ≫
          HomologicalComplex.homologyMap Fφ n := (Category.assoc _ _ _).symm
    _ = ((@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
          HomologicalComplex.homologyMap (GY N (YA A) g) n) ≫
          HomologicalComplex.homologyMap Fφ n :=
      congrArg (fun z => z ≫ HomologicalComplex.homologyMap Fφ n) h2
    _ = (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
          (HomologicalComplex.homologyMap (GY N (YA A) g) n ≫
          HomologicalComplex.homologyMap Fφ n) := Category.assoc _ _ _
    _ = (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
          (HomologicalComplex.homologyMap Fφ n ≫
          HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n) :=
      congrArg (fun z => (@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫ z) h4
    _ = ((@groupHomologyIso ℚ ↥N _ _ ι2 (Rep.res N.subtype A) n P).hom ≫
          HomologicalComplex.homologyMap Fφ n) ≫
          HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n := (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun z => z ≫ HomologicalComplex.homologyMap (GY N (Ygeo E A) g) n) h0

end Upstairs

end TernaryPeriodPolynomials.Argument.FiberModel
