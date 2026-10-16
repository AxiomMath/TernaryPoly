module

public import TernaryPeriodPolynomials.SymmetricSpace.EuclideanCoordinates
public import TernaryPeriodPolynomials.SymmetricSpace.ActionIsotopy
public import TernaryPeriodPolynomials.Topology.Euclidean.Local.Orientation

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceEuclideanCoordinates
open SymmetricSpacePositive EuclideanLocalHomology

/-- The actual normalized congruence action expressed in the global Euclidean coordinates. -/
def coordinateAction (g : RealGL) : EuclideanSpace ℝ (Fin 5) ≃ₜ EuclideanSpace ℝ (Fin 5) :=
  (spaceHomeomorph.symm.trans (actionHomeomorph g)).trans spaceHomeomorph

@[simp] theorem coordinateAction_apply (g : RealGL) (z : EuclideanSpace ℝ (Fin 5)) :
    coordinateAction g z = spaceHomeomorph (act g (spaceHomeomorph.symm z)) := rfl

/-- The actual Euclidean-coordinate isotopy of a path in the real matrix group. -/
def coordinateActionHomotopy {g : RealGL} (p : Path 1 g) :
    ContinuousMap.Homotopy (ContinuousMap.id _) (coordinateAction g).toHomotopyEquiv.toFun where
  toFun z := spaceHomeomorph (actionHomotopy p (z.1,spaceHomeomorph.symm z.2))
  continuous_toFun := by
    have h : Continuous (fun z : unitInterval × EuclideanSpace ℝ (Fin 5) =>
        actionHomotopy p (z.1,spaceHomeomorph.symm z.2)) :=
      (actionHomotopy p).continuous.comp
        (continuous_fst.prodMk (spaceHomeomorph.symm.continuous.comp continuous_snd))
    exact spaceHomeomorph.continuous.comp h
  map_zero_left z := by simp
  map_one_left z := by simp; rfl

/-- Every time slice in global Euclidean coordinates is a genuine injective map. -/
theorem coordinateActionHomotopy_injective {g : RealGL} (p : Path 1 g) (t : unitInterval) :
    Function.Injective (fun z => coordinateActionHomotopy p (t,z)) :=
  spaceHomeomorph.injective.comp ((actionHomotopy_injective p t).comp
    spaceHomeomorph.symm.injective)

/-- Every real-matrix path from identity preserves the genuine five-dimensional local
homology generators in the fixed global coordinates. -/
theorem coordinateAction_localGenerator {g : RealGL} (p : Path 1 g)
    (x : EuclideanSpace ℝ (Fin 5)) :
    HomologicalComplex.homologyMap
      (pointLocalMap (coordinateAction g).toHomotopyEquiv.toFun (coordinateAction g).injective x)
      5 (localGenerator 3 x) = localGenerator 3 (coordinateAction g x) :=
  pointLocalMap_generator 3 (coordinateAction g).toHomotopyEquiv.toFun
    (coordinateAction g).injective (coordinateActionHomotopy p)
      (coordinateActionHomotopy_injective p) x

end TernaryPoly.SymmetricSpaceEuclideanCoordinates
