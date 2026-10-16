module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingZeroExtension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.PolynomialExp
public import Mathlib.Data.Set.Pointwise.Support
public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.Topology.EMetricSpace.Paracompact
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
public import Mathlib.Topology.ShrinkingLemma

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter Function SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open scoped ContDiff Topology Manifold

instance quotientLocallyCompact : LocallyCompactSpace OrbitSpace :=
  ChartedSpace.locallyCompactSpace Coordinates OrbitSpace

instance quotientSigmaCompact : SigmaCompactSpace OrbitSpace := inferInstance

instance openQuotientLocallyCompact (O : TopologicalSpace.Opens OrbitSpace) : LocallyCompactSpace O :=
  O.isOpen.locallyCompactSpace

/-- A genuine smooth partition of unity on any closed quotient set covered by two opens. -/
theorem exists_quotient_partition {K U V : Set OrbitSpace} (hK : IsClosed K)
    (hU : IsOpen U) (hV : IsOpen V) (hKUV : K ⊆ U ∪ V) :
    ∃ f : SmoothPartitionOfUnity (Fin 2) 𝓘(ℝ, Coordinates) OrbitSpace K,
      f.IsSubordinate ![U, V] := by
  apply SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates) hK ![U, V]
  · intro i
    fin_cases i <;> assumption
  · intro q hq
    rcases hKUV hq with h | h
    · exact mem_iUnion.mpr ⟨0, h⟩
    · exact mem_iUnion.mpr ⟨1, h⟩

/-- The true open quotient submanifold on which an ordinary Mayer-Vietoris partition lives. -/
def unionOpen (U V : Set OrbitSpace) (hU : IsOpen U) (hV : IsOpen V) : TopologicalSpace.Opens OrbitSpace :=
  ⟨U ∪ V, hU.union hV⟩

/-- Partition of unity on the entire open union, obtained from Mathlib's actual manifold
partition construction on that open submanifold. -/
theorem exists_union_partition {U V : Set OrbitSpace} (hU : IsOpen U) (hV : IsOpen V) :
    ∃ f : SmoothPartitionOfUnity (Fin 2) 𝓘(ℝ, Coordinates) (unionOpen U V hU hV) univ,
      f.IsSubordinate (fun i => Subtype.val ⁻¹' (![U, V] i)) := by
  apply SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Coordinates) isClosed_univ
    (fun i => Subtype.val ⁻¹' (![U, V] i))
  · intro i
    fin_cases i
    · exact hU.preimage continuous_subtype_val
    · exact hV.preimage continuous_subtype_val
  · intro q _
    rcases q.property with h | h
    · exact mem_iUnion.mpr ⟨0, h⟩
    · exact mem_iUnion.mpr ⟨1, h⟩

/-- Extend a scalar from an actual open quotient submanifold by zero as an ambient function.
Its smoothness is asserted only on that open domain. -/
def openScalar (O : TopologicalSpace.Opens OrbitSpace) (f : O → ℝ) (q : OrbitSpace) : ℝ := by
  classical
  exact if hq : q ∈ O then f ⟨q, hq⟩ else 0

@[simp] theorem openScalar_apply (O : TopologicalSpace.Opens OrbitSpace) (f : O → ℝ)
    (q : O) : openScalar O f q = f q := by simp [openScalar]

theorem openScalar_smooth (O : TopologicalSpace.Opens OrbitSpace)
    (f : C^∞⟮𝓘(ℝ, Coordinates), O; 𝓘(ℝ), ℝ⟯) :
    ContMDiffOn 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (openScalar O f) O := by
  have hf : ContMDiff 𝓘(ℝ, Coordinates) 𝓘(ℝ) ∞ (fun q : O => openScalar O f q) := by
    simpa only [openScalar_apply] using f.contMDiff
  intro q hq
  exact (contMDiffAt_subtype_iff.mp (hf ⟨q, hq⟩)).contMDiffWithinAt

end TernaryPoly.SmoothDeRhamGluing
