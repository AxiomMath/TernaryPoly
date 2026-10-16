module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.SingularChains

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory Limits AlgebraicTopology HomologicalComplex
open scoped Simplicial

/-- Literal coefficient sum on genuine real singular zero-chains. -/
def realSingularSum (X : TopCat.{0}) : (realSingularChains X).X 0 ⟶ ModuleCat.of ℝ ℝ :=
  Sigma.desc (fun _ : (TopCat.toSSet.obj X) _⦋0⦌ => 𝟙 (ModuleCat.of ℝ ℝ))

/-- The scalar augmentation sends the coefficient on each actual vertex to itself. -/
theorem realSingularSum_generator (X : TopCat.{0}) (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    (TopCat.toSSet.obj X).ιChainComplex σ ≫ realSingularSum X = 𝟙 (ModuleCat.of ℝ ℝ) :=
  Sigma.ι_comp_desc _ _

/-- Degree-zero class formation commutes with the literal chain generator. -/
theorem realZeroClass_precompose (K : ChainComplex (ModuleCat ℝ) ℕ)
    {M : ModuleCat ℝ} (k : M ⟶ K.X 0) :
    k ≫ realZeroClass K = K.liftCycles k 0 (by simp) (by simp) ≫ K.homologyπ 0 := by
  unfold realZeroClass
  rw [← Category.assoc]
  congr 1
  apply (cancel_mono (K.iCycles 0)).mp
  simp only [Category.assoc, liftCycles_i, Category.comp_id]

/-- The literal scalar sum is the genuine H0 augmentation composed with class formation. -/
theorem realSingularSum_eq_class (X : TopCat.{0}) :
    realSingularSum X = realZeroClass (realSingularChains X) ≫
      X.singularHomology₀ε (ModuleCat.of ℝ ℝ) := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  rw [realSingularSum_generator]
  erw [← Category.assoc, realZeroClass_precompose]
  exact ((TopCat.toSSet.obj X).liftCycles_ιChainComplex_homologyπ_homology₀ε
    (ModuleCat.of ℝ ℝ) σ).symm

/-- Boundaries have zero literal coefficient sum. -/
theorem realSingularSum_boundary (X : TopCat.{0}) :
    (realSingularChains X).d 1 0 ≫ realSingularSum X = 0 := by
  rw [realSingularSum_eq_class]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change X.singularHomology₀ε (ModuleCat.of ℝ ℝ)
    (realZeroClass (realSingularChains X) ((realSingularChains X).d 1 0 c)) = 0
  rw [(realZeroClass_eq_zero _ _).mpr ⟨c, rfl⟩]
  exact map_zero (X.singularHomology₀ε (ModuleCat.of ℝ ℝ)).hom

/-- On a path-connected space, the actual augmented real singular chain sequence is exact. -/
theorem realSingularSum_exact (X : TopCat.{0}) [PathConnectedSpace X] :
    LinearMap.range ((realSingularChains X).d 1 0).hom = LinearMap.ker (realSingularSum X).hom := by
  ext c
  rw [LinearMap.mem_ker, realSingularSum_eq_class]
  change c ∈ LinearMap.range ((realSingularChains X).d 1 0).hom ↔
    X.singularHomology₀ε (ModuleCat.of ℝ ℝ) (realZeroClass (realSingularChains X) c) = 0
  rw [← realZeroClass_eq_zero]
  constructor
  · intro h
    rw [h]
    exact map_zero (X.singularHomology₀ε (ModuleCat.of ℝ ℝ)).hom
  · intro h
    apply (ModuleCat.mono_iff_injective (X.singularHomology₀ε (ModuleCat.of ℝ ℝ))).mp inferInstance
    exact h.trans (map_zero (X.singularHomology₀ε (ModuleCat.of ℝ ℝ)).hom).symm

/-- The literal scalar augmentation is surjective on every nonempty space. -/
theorem realSingularSum_surjective (X : TopCat.{0}) [Nonempty X] :
    Function.Surjective (realSingularSum X) := by
  obtain ⟨x⟩ := ‹Nonempty X›
  let σ : (TopCat.toSSet.obj X) _⦋0⦌ :=
    (TopCat.toSSetObjEquiv X _).symm (ContinuousMap.const _ x)
  intro r
  refine ⟨((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℝ ℝ) σ) r, ?_⟩
  exact congrArg (fun f => f r) (realSingularSum_generator X σ)

/-- The literal scalar augmentation is natural for every continuous map. -/
theorem realSingularSum_natural {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (realSingularChainMap f).f 0 ≫ realSingularSum Y = realSingularSum X := by
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  erw [← Category.assoc]
  have h := SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y) (TopCat.toSSet.map f) (ModuleCat.of ℝ ℝ) σ
  change (TopCat.toSSet.obj X).ιChainComplex σ ≫ (realSingularChainMap f).f 0 = _ at h
  erw [h, realSingularSum_generator, realSingularSum_generator]

end TernaryPoly.SmoothSingularComparison
