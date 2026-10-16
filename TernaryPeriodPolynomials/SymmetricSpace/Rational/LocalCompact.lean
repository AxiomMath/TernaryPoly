module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingGlueData
public import Mathlib.Topology.Compactness.LocallyCompact

@[expose] public section


namespace TernaryPoly.SymmetricSpaceRationalGluing
open Topology TopologicalSpace SymmetricSpaceFlagCoordinates

/-- Each closed root half-line has its usual locally compact topology. -/
theorem halfLineLocallyCompact : LocallyCompactSpace HalfLine :=
  isClosed_Ici.locallyCompactSpace

/-- The actual full corner chart, with both zero-root faces, is locally compact. -/
theorem cornerLocallyCompact : LocallyCompactSpace Corner := by
  let := halfLineLocallyCompact
  infer_instance

/-- The rational gluing inherits local compactness from its genuine open corner charts. -/
instance gluedLocallyCompact : LocallyCompactSpace Glued where
  local_compact_nhds := by
    let := cornerLocallyCompact
    intro x N hN
    obtain ⟨g,p,rfl⟩ := chart_jointly_surjective x
    obtain ⟨K,hK,hKN,hKc⟩ := local_compact_nhds ((continuous_chart g).continuousAt hN)
    exact ⟨chart g '' K,(chart_isOpenEmbedding g).isOpenMap.image_mem_nhds hK,
      Set.image_subset_iff.mpr hKN,hKc.image (continuous_chart g)⟩

end TernaryPoly.SymmetricSpaceRationalGluing
