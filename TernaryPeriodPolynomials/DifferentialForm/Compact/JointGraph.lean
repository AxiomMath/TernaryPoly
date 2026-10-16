module

public import TernaryPeriodPolynomials.DifferentialForm.Compact.ChartPartitionHilbert
public import TernaryPeriodPolynomials.DifferentialForm.Chart.JointLimit
public import TernaryPeriodPolynomials.DifferentialForm.JointGraph.Maximal
public import TernaryPeriodPolynomials.Analysis.JointGraphFiniteReconstruction

@[expose] public section


/-! Every actual simultaneous maximal graph triple with compact weak support is a joint compact graph limit. -/
noncomputable section
namespace TernaryPoly.PolynomialFormHilbert
open Set PolynomialFormCoordinates PolynomialFormConnection SymmetricSpaceCovering
attribute [local instance] cutoffHilbertModule
attribute [local irreducible] maximalDifferential maximalCodifferential

theorem compact_weak_triple_mem_jointGraphClosure (n k : ℕ) (K : Set OrbitSpace) (hK : IsCompact K)
    (x : Hilbert n (k+1)) (y : Hilbert n ((k+1)+1)) (z : Hilbert n k)
    (hx : HasWeakSupportIn n (k+1) K x)
    (hy : (x,y) ∈ (maximalDifferential n (k+1)).graph)
    (hz : (x,z) ∈ (maximalCodifferential n k).graph) :
    (x,y,z) ∈ jointGraphClosure n k := by
  let p : CompactChartPartitionData K := Classical.choice (exists_compactChartPartitionData K hK)
  have H := p.exists_hilbert_limits n (k+1)
  let L := H.choose
  have hi (i : p.charts) : ∃ v : Hilbert n ((k+1)+1), ∃ w : Hilbert n k,
      (L i x,v,w) ∈ jointGraphClosure n k :=
    chartLimit_mem_jointGraphClosure n k i.val (p.cutoff i).inner (p.cutoff i).outer
      (p.cutoff i).inner_smooth (p.cutoff i).inner_compact (p.cutoff i).inner_support
      (p.cutoff i).outer_smooth (p.cutoff i).outer_compact (p.cutoff i).outer_support
      (L i) (H.choose_spec.1 i) x y z hy hz
  exact JointGraphFiniteReconstruction.mem_of_finite_reconstruction (jointGraphClosure n k)
    (maximalDifferential n (k+1)) (maximalCodifferential n k)
    (fun _ _ _ h => jointGraphClosure_mem_maximal n k h) (fun i : p.charts => L i x) x y z hi
    (H.choose_spec.2.2 x hx) hy hz

end TernaryPoly.PolynomialFormHilbert
