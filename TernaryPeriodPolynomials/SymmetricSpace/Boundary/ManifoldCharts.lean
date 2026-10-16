module

public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryProduct
public import TernaryPeriodPolynomials.SymmetricSpace.Quotient.BoundaryStrip
public import TernaryPeriodPolynomials.Topology.Singular.BoundaryRestrictionGeometry

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceBoundaryManifold
open SymmetricSpaceRationalGluing SymmetricSpaceBordifiedQuotient
  SymmetricSpaceBordifiedPrincipalSix IntegralGL3Congruence SymmetricSpaceBoundaryCharts
  SymmetricSpaceQuotientBoundary SingularBoundaryRestriction

/-- Restrict the literal quotient product chart to its exact height-zero boundary slice. -/
def boundaryChart (x : Glued) : OpenPartialHomeomorph BoundaryBase BoundaryCoordinates where
  toFun q := (productChart x q.val).1
  invFun v := ⟨(productChart x).symm (v, heightZero),
    (productChart_symm_boundary x (v, heightZero)).mpr rfl⟩
  source := Subtype.val ⁻¹' (productChart x).source
  target := (fun v => (v, heightZero)) ⁻¹' (productChart x).target
  map_source' q hq := by
    have hz : (productChart x q.val).2 = heightZero :=
      Subtype.ext ((productChart_boundary x hq).mp q.property)
    change ((productChart x q.val).1, heightZero) ∈ (productChart x).target
    rw [← hz]
    exact (productChart x).map_source hq
  map_target' v hv := (productChart x).map_target hv
  left_inv' q hq := by
    apply Subtype.ext
    have hz : (productChart x q.val).2 = heightZero :=
      Subtype.ext ((productChart_boundary x hq).mp q.property)
    change (productChart x).symm ((productChart x q.val).1, heightZero) = q.val
    rw [← hz]
    exact (productChart x).left_inv hq
  right_inv' v hv := congrArg Prod.fst ((productChart x).right_inv hv)
  open_source := (productChart x).open_source.preimage continuous_subtype_val
  open_target := (productChart x).open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun := continuous_fst.comp_continuousOn
    ((productChart x).continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h))
  continuousOn_invFun := by
    intro v hv
    apply tendsto_subtype_rng.mpr
    exact ((productChart x).symm.continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ h => h)) v hv

@[simp] theorem boundaryChart_source (x : Glued) :
    (boundaryChart x).source = Subtype.val ⁻¹' (productChart x).source := rfl

@[simp] theorem boundaryChart_apply (x : Glued) (q : BoundaryBase) :
    boundaryChart x q = (productChart x q.val).1 := rfl

@[simp] theorem boundaryChart_symm_apply (x : Glued) (v : BoundaryCoordinates) :
    ((boundaryChart x).symm v).val = (productChart x).symm (v, heightZero) := rfl

/-- The actual boundary subtype is covered by the restricted Euclidean-four-coordinate charts. -/
theorem charts_cover (q : BoundaryBase) : ∃ x : Glued, q ∈ (boundaryChart x).source :=
  productCharts_cover q.val

/-- The exact four-dimensional boundary atlas. -/
instance boundaryChartedSpace : ChartedSpace BoundaryCoordinates BoundaryBase where
  atlas := Set.range boundaryChart
  chartAt q := boundaryChart (charts_cover q).choose
  mem_chart_source q := (charts_cover q).choose_spec
  chart_mem_atlas q := ⟨(charts_cover q).choose, rfl⟩

/-- The quotient boundary is Hausdorff as its literal subtype of the actual Hausdorff quotient. -/
instance boundaryHausdorff : T2Space BoundaryBase := by
  let := SymmetricSpaceCompactBordification.quotient_hausdorff principalSix
  infer_instance

/-- The actual boundary subtype is second countable. -/
instance boundarySecondCountable : SecondCountableTopology BoundaryBase := inferInstance

/-- The actual whole boundary is compact. -/
instance boundaryCompact : CompactSpace BoundaryBase :=
  isCompact_iff_compactSpace.mp
    SymmetricSpaceCompactBordification.actual_compact_bordification.2.2.2.1

/-- The coordinate model is genuinely Euclidean four-space. -/
def boundaryEuclidean : BoundaryCoordinates ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).toHomeomorph.symm

end TernaryPoly.SymmetricSpaceBoundaryManifold
