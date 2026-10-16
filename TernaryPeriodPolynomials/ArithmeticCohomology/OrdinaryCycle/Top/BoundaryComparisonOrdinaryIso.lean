module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonLowHomology
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Top.BoundaryComparisonEvaluationIso

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryTopBoundaryComparison
open CategoryTheory Limits HomologicalComplex IntegralGL3Congruence
open EquivariantSingularSmall SymmetricSpaceBoundaryIncidenceHomology

/-- The canonical H2 evaluator for the genuine arithmetic relative chains is an isomorphism. -/
theorem upstairsHomologyEvaluation_isIso (W : Rep.{0} ℚ principalSix) :
    IsIso (homologyEvaluation upstairsRelativeChains W 2) := by
  let : Projective (upstairsRelativeChains.X 0) := upstairsRelativeDegree_projective 0
  let : Projective (upstairsRelativeChains.X 1) := upstairsRelativeDegree_projective 1
  let : Projective (upstairsRelativeChains.cycles 0) :=
    Projective.of_iso upstairsRelativeChains.cycles₀Iso.symm inferInstance
  have h0 : upstairsRelativeChains.ExactAt 0 :=
    (exactAt_iff_isZero_homology _ _).mpr upstairsRelativeH0_isZero
  have h1 : upstairsRelativeChains.ExactAt 1 :=
    (exactAt_iff_isZero_homology _ _).mpr upstairsRelativeH1_isZero
  let : Projective (upstairsRelativeChains.cycles 1) := cycleProjective_next upstairsRelativeChains 0 h0
  let s0 := cycleSequenceSplitting upstairsRelativeChains 0 h0
  let s1 := cycleSequenceSplitting upstairsRelativeChains 1 h1
  exact homologyEvaluationTwo_isIso upstairsRelativeChains W s1 s0.r s0.f_r

/-- Ordinary equivariant functionals use the actual principal-six action on incidence cycles. -/
abbrev ordinaryFunctionals (W : Rep.{0} ℚ principalSix) := ModuleCat.of ℚ (ordinaryCyclesRep ⟶ W)

/-- Precomposition by the actual relative-to-ordinary inverse gives the literal functional iso. -/
def relativeOrdinaryFunctionalIso (W : Rep.{0} ℚ principalSix) :
    ModuleCat.of ℚ (upstairsRelativeChains.homology 2 ⟶ W) ≅ ordinaryFunctionals W where
  hom := ModuleCat.ofHom {
    toFun := fun φ => upstairsRelativeH2OrdinaryIso.inv ≫ φ
    map_add' := fun _ _ => by simp only [Preadditive.comp_add]
    map_smul' := fun _ _ => by simp only [Linear.comp_smul, RingHom.id_apply] }
  inv := ModuleCat.ofHom {
    toFun := fun φ => upstairsRelativeH2OrdinaryIso.hom ≫ φ
    map_add' := fun _ _ => by simp only [Preadditive.comp_add]
    map_smul' := fun _ _ => by simp only [Linear.comp_smul, RingHom.id_apply] }
  hom_inv_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change upstairsRelativeH2OrdinaryIso.hom ≫ (upstairsRelativeH2OrdinaryIso.inv ≫ φ) = φ
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  inv_hom_id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    change upstairsRelativeH2OrdinaryIso.inv ≫ (upstairsRelativeH2OrdinaryIso.hom ≫ φ) = φ
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual relative Hom cohomology is canonically identified with ordinary functionals. -/
def relativeOrdinaryCohomologyIso (W : Rep.{0} ℚ principalSix) :
    (homCochains upstairsRelativeChains W).homology 2 ≅ ordinaryFunctionals W := by
  let := upstairsHomologyEvaluation_isIso W
  exact asIso (homologyEvaluation upstairsRelativeChains W 2) ≪≫ relativeOrdinaryFunctionalIso W

/-- The ordinary functional is literally evaluated after the actual inverse relative/MV map. -/
theorem relativeOrdinaryCohomologyIso_apply (W : Rep.{0} ℚ principalSix)
    (x : (homCochains upstairsRelativeChains W).homology 2) :
    (relativeOrdinaryCohomologyIso W).hom x =
      upstairsRelativeH2OrdinaryIso.inv ≫ homologyEvaluation upstairsRelativeChains W 2 x := rfl

end TernaryPoly.OrdinaryTopBoundaryComparison
