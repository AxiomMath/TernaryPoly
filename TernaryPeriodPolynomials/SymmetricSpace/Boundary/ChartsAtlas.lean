module

public import TernaryPeriodPolynomials.SymmetricSpace.Boundary.ChartsModel
public import TernaryPeriodPolynomials.SymmetricSpace.Corner.Separation
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingInterior
public import Mathlib.Geometry.Manifold.ChartedSpace

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryCharts
open Topology SymmetricSpaceFlagCoordinates SymmetricSpaceRationalAction SymmetricSpaceRationalGluing

/-- The actual rational-chart parametrization by the standard half-space. -/
def halfSpaceParam (g : RationalGL) : EuclideanHalfSpace 5 → Glued :=
  chart g ∘ cornerHalfSpaceHomeomorph.symm

theorem halfSpaceParam_isOpenEmbedding (g : RationalGL) : IsOpenEmbedding (halfSpaceParam g) :=
  (chart_isOpenEmbedding g).comp cornerHalfSpaceHomeomorph.symm.isOpenEmbedding

@[simp] theorem halfSpaceParam_range (g : RationalGL) :
    Set.range (halfSpaceParam g)=Set.range (chart g) := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨cornerHalfSpaceHomeomorph.symm p,rfl⟩
  · rintro ⟨p,rfl⟩
    exact ⟨cornerHalfSpaceHomeomorph p,by simp [halfSpaceParam]⟩

/-- A genuine open partial homeomorphism from the glued space to the standard half-space. -/
def halfSpaceChart (g : RationalGL) : OpenPartialHomeomorph Glued (EuclideanHalfSpace 5) :=
  ((halfSpaceParam_isOpenEmbedding g).toOpenPartialHomeomorph (halfSpaceParam g)).symm

@[simp] theorem halfSpaceChart_source (g : RationalGL) :
    (halfSpaceChart g).source=Set.range (chart g) := by
  simp [halfSpaceChart]

@[simp] theorem halfSpaceChart_target (g : RationalGL) :
    (halfSpaceChart g).target=Set.univ := by
  simp [halfSpaceChart]

@[simp] theorem halfSpaceChart_symm_apply (g : RationalGL) (p : EuclideanHalfSpace 5) :
    (halfSpaceChart g).symm p=halfSpaceParam g p := rfl

@[simp] theorem halfSpaceChart_apply_chart (g : RationalGL) (p : Corner) :
    halfSpaceChart g (chart g p)=cornerHalfSpaceHomeomorph p := by
  have h := (halfSpaceParam_isOpenEmbedding g).toOpenPartialHomeomorph_left_inv
    (halfSpaceParam g) (x:=cornerHalfSpaceHomeomorph p)
  simpa only [halfSpaceChart,halfSpaceParam,Function.comp_apply,Homeomorph.symm_apply_apply] using h

/-- Select a member of the actual rational chart cover. -/
def selectedFrame (x : Glued) : RationalGL := (chart_jointly_surjective x).choose

def selectedPoint (x : Glued) : Corner := (chart_jointly_surjective x).choose_spec.choose

theorem chart_selectedPoint (x : Glued) : chart (selectedFrame x) (selectedPoint x)=x :=
  (chart_jointly_surjective x).choose_spec.choose_spec

/-- The existing topology on the actual Hausdorff gluing carries standard half-space charts. -/
instance chartedSpace : ChartedSpace (EuclideanHalfSpace 5) Glued where
  atlas := Set.range halfSpaceChart
  chartAt x := halfSpaceChart (selectedFrame x)
  mem_chart_source x := by
    rw [halfSpaceChart_source]
    exact ⟨selectedPoint x,chart_selectedPoint x⟩
  chart_mem_atlas x := ⟨selectedFrame x,rfl⟩

@[simp] theorem chartAt_eq (x : Glued) :
    chartAt (EuclideanHalfSpace 5) x=halfSpaceChart (selectedFrame x) := rfl

@[simp] theorem chartAt_apply (x : Glued) :
    chartAt (EuclideanHalfSpace 5) x x=cornerHalfSpaceHomeomorph (selectedPoint x) := by
  change halfSpaceChart (selectedFrame x) x=_
  calc
    halfSpaceChart (selectedFrame x) x=
        halfSpaceChart (selectedFrame x) (chart (selectedFrame x) (selectedPoint x)) :=
      congrArg (halfSpaceChart (selectedFrame x)) (chart_selectedPoint x).symm
    _=cornerHalfSpaceHomeomorph (selectedPoint x) :=
      halfSpaceChart_apply_chart _ _

end TernaryPoly.SymmetricSpaceBoundaryCharts
