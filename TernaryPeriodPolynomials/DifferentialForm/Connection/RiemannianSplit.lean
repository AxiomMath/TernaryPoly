module

public import TernaryPeriodPolynomials.DifferentialForm.Connection.RiemannianFinite
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section


/-! Genuine short Riemannian paths give the ball-splitting property needed for properness. -/
noncomputable section
namespace TernaryPoly.SymmetricSpaceRiemannian
open SymmetricSpacePositive SymmetricSpaceCharts SymmetricSpaceCovering SymmetricSpaceQuotientManifold
open Manifold Set
open scoped ContDiff Manifold Bundle ENNReal
attribute [local instance] spaceMetricSpace

theorem space_dist_split (S T : Space) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s)
    (hST : dist S T < r + s) :
    ∃ U : Space, dist S U ≤ r ∧ dist U T < s := by
  by_cases hsmall : dist S T ≤ r
  · exact ⟨T, hsmall, by simpa using hs⟩
  have hlt : riemannianEDist 𝓘(ℝ, Coordinates) S T < ENNReal.ofReal (r + s) := by
    change edist S T < ENNReal.ofReal (r + s)
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff (by linarith)]
    exact hST
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_lt_of_riemannianEDist_lt hlt
  have hc : ContinuousOn (fun t => dist S (γ t)) (Icc (0 : ℝ) 1) :=
    continuous_dist.comp_continuousOn (continuousOn_const.prodMk hγ.continuousOn)
  obtain ⟨t, ht, he⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hc
    (show r ∈ Icc (dist S (γ 0)) (dist S (γ 1)) by
      rw [h0, h1, dist_self]
      exact ⟨hr, (lt_of_not_ge hsmall).le⟩)
  change dist S (γ t) = r at he
  refine ⟨γ t, he.le, ?_⟩
  have hleft := riemannianEDist_le_pathELength
    (hγ.mono (Icc_subset_Icc_right ht.2)) h0 (rfl : γ t = γ t) ht.1
  have hright := riemannianEDist_le_pathELength
    (hγ.mono (Icc_subset_Icc_left ht.1)) (rfl : γ t = γ t) h1 ht.2
  have hsum : edist S (γ t) + edist (γ t) T < ENNReal.ofReal (r + s) := by
    calc
      _ ≤ pathELength 𝓘(ℝ, Coordinates) γ 0 t + pathELength 𝓘(ℝ, Coordinates) γ t 1 := add_le_add hleft hright
      _ = pathELength 𝓘(ℝ, Coordinates) γ 0 1 := pathELength_add ht.1 ht.2
      _ < _ := hlen
  rw [edist_dist S (γ t), he, ENNReal.ofReal_add hr hs.le,
    ENNReal.add_lt_add_iff_left ENNReal.ofReal_ne_top, edist_dist, ENNReal.ofReal_lt_ofReal_iff hs] at hsum
  exact hsum

end TernaryPoly.SymmetricSpaceRiemannian
