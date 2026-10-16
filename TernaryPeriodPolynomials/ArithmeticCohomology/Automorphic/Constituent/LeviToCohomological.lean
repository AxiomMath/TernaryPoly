module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Constituent.LeviToCohomologicalAux
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.Petersson
public import TernaryPeriodPolynomials.ArithmeticCohomology.Automorphic.SmoothVectors
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.Source.GoodPlaneSourceData
public import TernaryPeriodPolynomials.ArithmeticCohomology.MultiplicityOne.Basic

@[expose] public section


/-!
# From an analytic Levi cocycle datum to `Cohomological`

A `LevelLeviCocycleData σ n` is a cocycle `α` for the twisted action `binaryCohomologicalAction`
whose coefficients are realized by smooth vectors `lift μ g`, smooth in `g` and fixed by the level
`{k ∈ GL₂(ℤ̂) : k₁₀ ≡ 0, k₁₁ ≡ 1 (mod 3)}`.  With the level group `K'` as the open compact
subgroup, the datum gives every clause of `Cohomological σ n` except non-triviality of the class,
which is a hypothesis:

* the coefficients of each `α g` are cusp functions, by `lift_realize`;
* the two-variable smooth lift is `exists_smooth_translate` (the cocycle identity expresses the
  translate through `α (g * h)` and `α g`);
* `α g` is right invariant under `K'`, by the equivariance of `realize` and `level`;
* the cocycle identity is a field.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Adelic
open TernaryPeriodPolynomials.Automorphic.SmoothVectors
  (integralLevel integralLevel_isOpenCompact)
open TernaryPeriodPolynomials.CuspIntegral (levelGroup mem_levelGroup_iff redGL)
open TernaryPeriodPolynomials.LevelThreeSource (LevelLeviCocycleData)
open TernaryPeriodPolynomials.MultiplicityOne (mem_levelThreeValues)
open TernaryPeriodPolynomials.Separation (PlaneLeviLevel)

namespace TernaryPeriodPolynomials.Automorphic.Constituent

/-- The level group `K'` is an open compact subgroup of `GL₂(𝔸_f)`. -/
theorem levelGroup_open_compact :
    IsOpen (levelGroup : Set BinaryFiniteGL) ∧ IsCompact (levelGroup : Set BinaryFiniteGL) := by
  have hopen : IsOpen (levelGroup : Set BinaryFiniteGL) := Petersson.isOpen_levelGroup
  have hle : (levelGroup : Set BinaryFiniteGL) ⊆ (integralLevel : Set BinaryFiniteGL) := by
    intro κ hκ
    have hκ' : κ ∈ levelGroup := hκ
    obtain ⟨m, -, rfl⟩ := Subgroup.mem_map.mp hκ'
    exact ⟨m, rfl⟩
  exact ⟨hopen, integralLevel_isOpenCompact.2.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ hopen) hle⟩

/-- An element of the level group `K'` is the image of an integral matrix of the Levi level. -/
theorem exists_planeLeviLevel_of_mem_levelGroup {k : BinaryFiniteGL} (hk : k ∈ levelGroup) :
    ∃ m : Matrix.GeneralLinearGroup (Fin 2) IntegralAdeles,
      Matrix.GeneralLinearGroup.map integralEmbedding m = k ∧ PlaneLeviLevel m := by
  obtain ⟨m, hm, hrow⟩ := (mem_levelGroup_iff k).mp hk
  have h0 : (redGL m).val 1 0 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congrFun hrow 0
  have h1 : (redGL m).val 1 1 = 1 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congrFun hrow 1
  exact ⟨m, hm, h0, h1⟩

/-- **Level invariance**: the cocycle is right invariant under the level group `K'`. -/
theorem levelGroup_fixes {σ : CuspidalRepresentation} {n : ℕ} (E : LevelLeviCocycleData σ n)
    (u : levelGroup) (g : BinaryRealGL) (x : BinaryAdelicGL) :
    E.α g (x * atFinite u.val) = E.α g x := by
  apply Subtype.ext
  apply MvPolynomial.ext
  intro μ
  obtain ⟨m, hm, hlevel⟩ := exists_planeLeviLevel_of_mem_levelGroup u.property
  have hfix : σ.π (atFinite u.val) (E.lift μ g).val = (E.lift μ g).val := by
    rw [← hm]
    exact (mem_levelThreeValues.mp (E.level μ g)) m hlevel
  have hsub : (⟨σ.π (atFinite u.val) (E.lift μ g).val,
      σ.smooth_stable _ _ (E.lift μ g).property⟩ : σ.smooth) = E.lift μ g := Subtype.ext hfix
  refine (E.lift_realize μ g (x * atFinite u.val)).symm.trans (Eq.trans ?_
    (E.lift_realize μ g x))
  exact ((σ.equivariant (atFinite u.val) (E.lift μ g) x).symm).trans
    (congrArg (fun w => σ.realize w x) hsub)

/-- **An analytic Levi cocycle datum with non-trivial class is a `Cohomological` witness.** The
cocycle is `E.α`; the open compact subgroup is the level group `K'`. -/
theorem cohomological_of_leviData {σ : CuspidalRepresentation} {n : ℕ}
    (E : LevelLeviCocycleData σ n)
    (noncob : ¬ ∃ v : BinaryAdelicGL → Binary.HomogeneousPoly (n + 1),
      BinaryValues σ n v ∧ ∀ g x, E.α g x = binaryCohomologicalAction n g v x - v x) :
    Cohomological σ n := by
  refine ⟨E.α, ?_, ?_, ⟨levelGroup, levelGroup_open_compact.1, levelGroup_open_compact.2,
    fun u g x => levelGroup_fixes E u g x⟩, E.cocycle, noncob⟩
  · intro g μ
    exact LinearMap.mem_range.mpr ⟨E.lift μ g, funext fun A => E.lift_realize μ g A⟩
  · intro μ
    exact exists_smooth_translate E.α E.cocycle E.lift E.lift_realize E.lift_smooth μ

end TernaryPeriodPolynomials.Automorphic.Constituent

end
