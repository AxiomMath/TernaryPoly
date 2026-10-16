module

public import TernaryPeriodPolynomials.Topology.Rational.Manifold.CompactClasses
public import TernaryPeriodPolynomials.Topology.Euclidean.Convex.LocalHomology
public import TernaryPeriodPolynomials.Topology.Rational.Chart.CompactSupportNaturality
public import TernaryPeriodPolynomials.SymmetricSpace.HalfSpace.BoundaryOrientationGlobal

@[expose] public section


/-!
# Top homology of a connected compact oriented manifold is spanned by the fundamental class

For a compact Hausdorff space `X` charted over `H ≃ₜ ℝ^{n+2}` with a homological orientation
`o` (`TernaryPoly.RationalLocalOrientation.Orientation`) and `X` connected,
`H_{n+2}(X; ℚ)` is spanned by the fundamental class:

* `chart_convex_point_injective`: inside one chart, top homology supported on a compact set with convex
  chart image maps injectively to the local homology at any of its points (Hatcher, proof of
  Lemma 3.27, from the Euclidean convex case and the chart comparison of the original library);
* `local_top_scalar`: the local top homology is spanned by any nonzero class;
* `exists_nbhd_scalar_eq`: the coefficient of a global class against the orientation is locally
  constant;
* `top_homology_eq_smul_fundamental` (support model) and `chains_top_homology_eq_smul` (absolute
  chains): every top class is a rational multiple of the fundamental class.

General and reusable: nothing here is specific to the arithmetic boundary; see
`FacePairingFull/Comparison/BoundaryTopClass.lean` for the application to `∂M`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits HomologicalComplex
open TernaryPoly TernaryPoly.RationalRelativeSingular TernaryPoly.RationalLocalChartHomology
  TernaryPoly.RationalLocalOrientation TernaryPoly.RationalChartCompactSupport
  TernaryPoly.EuclideanConvexLocal

noncomputable section

namespace TernaryPeriodPolynomials.Argument.TopHomology

variable {X : Type} [TopologicalSpace X] [T2Space X] (n : ℕ)

/-- Inside one chart, the top homology supported on a compact set with convex chart image maps
injectively to the local homology at any of its points. -/
theorem chart_convex_point_injective (e : OpenPartialHomeomorph X (EuclideanSpace ℝ (Fin (n+2))))
    (K : Set X) (hK : IsCompact K) (hKs : K ⊆ e.source)
    (hconv : Convex ℝ (e '' K)) (x : X) (hx : x ∈ K) :
    Function.Injective (homologyMap (supportPointMap K x hx) (n+2)) := by
  intro c d hcd
  have hiso : Function.Injective (chartSupportHomologyIso e K hK hKs (n+2)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  apply hiso
  have hK' := RationalChartCompactSupport.image_isCompact e K hK hKs
  have hinj : Function.Injective (homologyMap (pointMap (e '' K) (e x) ⟨x, hx, rfl⟩) (n+2)) :=
    (ModuleCat.mono_iff_injective _).mp
      (inferInstance : Mono (pointHomologyIso (e '' K) hK' hconv (e x) ⟨x, hx, rfl⟩ (n+2)).hom)
  apply hinj
  have h1 := chartSupportHomologyIso_point_apply e K hK hKs x hx (n+2) c
  have h2 := chartSupportHomologyIso_point_apply e K hK hKs x hx (n+2) d
  change homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) (n+2) _ =
    homologyMap (supportPointMap (e '' K) (e x) ⟨x, hx, rfl⟩) (n+2) _
  rw [h1, h2, hcd]


variable {H : Type} [TopologicalSpace H] [ChartedSpace H X]

/-- The local top homology at a point of a Euclidean-charted manifold is spanned by any nonzero
class. -/
theorem local_top_scalar (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (x : X)
    (g a : (localChains x).homology (n+2)) (hg : g ≠ 0) : ∃ q : ℚ, a = q • g := by
  let f := (chartAt H x).transHomeomorph e
  have hx : x ∈ f.source := by
    simp [f, mem_chart_source]
  let φ := (euclideanChartLocalTopIso n f x hx).toLinearEquiv
  have hφg : φ g ≠ 0 := by
    intro h; exact hg (φ.injective (by simpa using h))
  refine ⟨φ a / φ g, ?_⟩
  apply φ.injective
  rw [map_smul]
  simp only [smul_eq_mul]
  field_simp


open TernaryPoly.RationalManifoldCompact in
/-- **Local constancy of the coefficient of a global top class.** -/
theorem exists_nbhd_scalar_eq (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2)))
    (o : Orientation (n+2) X) (F c : (supportChains (Set.univ : Set X)).homology (n+2))
    (hF : ∀ (x : X) (hx : x ∈ (Set.univ : Set X)),
      homologyMap (supportPointMap Set.univ x hx) (n+2) F = o.generator x)
    (q : X → ℚ)
    (hq : ∀ x (hx : x ∈ (Set.univ : Set X)),
      homologyMap (supportPointMap Set.univ x hx) (n+2) c = q x • o.generator x) (x : X) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∀ y ∈ V, q y = q x := by
  let f := (chartAt H x).transHomeomorph e
  have hxs : x ∈ f.source := by simp [f, mem_chart_source]
  have hxt : f x ∈ f.target := f.map_source hxs
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp f.open_target (f x) hxt
  let B : Set (EuclideanSpace ℝ (Fin (n+2))) := Metric.closedBall (f x) (r / 2)
  have hBt : B ⊆ f.target := fun z hz =>
    hball (lt_of_le_of_lt (by simpa [B, Metric.mem_closedBall] using hz) (by linarith : r / 2 < r) |>
      fun h => by simpa [Metric.mem_ball] using h)
  let K : Set X := f.symm '' B
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hK : IsCompact K := hBc.image_of_continuousOn (f.symm.continuousOn.mono hBt)
  have hKs : K ⊆ f.source := by
    rintro _ ⟨z, hz, rfl⟩
    exact OpenPartialHomeomorph.mapsTo_symm f (hBt hz)
  have hfK : f '' K = B := by
    rw [Set.image_image]
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      show f (f.symm w) ∈ B
      rw [f.right_inv (hBt hw)]
      exact hw
    · intro hz
      exact ⟨z, hz, f.right_inv (hBt hz)⟩
  have hconv : Convex ℝ (f '' K) := by
    rw [hfK]; exact convex_closedBall _ _
  have hxB : f x ∈ B := by simp [B, Metric.mem_closedBall]; positivity
  have hxK : x ∈ K := ⟨f x, hxB, f.left_inv hxs⟩
  let V : Set X := f.source ∩ f ⁻¹' Metric.ball (f x) (r / 2)
  have hVo : IsOpen V := f.continuousOn.isOpen_inter_preimage f.open_source Metric.isOpen_ball
  have hxV : x ∈ V := ⟨hxs, by simp [Metric.mem_ball]; positivity⟩
  have hVK : V ⊆ K := by
    rintro y ⟨hys, hyb⟩
    exact ⟨f y, Metric.ball_subset_closedBall hyb, f.left_inv hys⟩
  refine ⟨V, hVo, hxV, fun y hy => ?_⟩
  have hyK : y ∈ K := hVK hy
  let rK := homologyMap (supportRestriction Set.univ K (Set.subset_univ K)) (n+2)
  have hptc : ∀ z (hz : z ∈ K), homologyMap (supportPointMap K z hz) (n+2) (rK c) = q z • o.generator z := by
    intro z hz
    rw [TernaryPoly.RationalManifoldCompact.restriction_point_apply Set.univ K (Set.subset_univ K) z hz
      (n+2) c]
    exact hq z trivial
  have hptF : ∀ z (hz : z ∈ K), homologyMap (supportPointMap K z hz) (n+2) (rK F) = o.generator z := by
    intro z hz
    rw [TernaryPoly.RationalManifoldCompact.restriction_point_apply Set.univ K (Set.subset_univ K) z hz
      (n+2) F]
    exact hF z trivial
  have hzero : rK c = q x • rK F := by
    have hinj := chart_convex_point_injective n f K hK hKs hconv x hxK
    apply hinj
    rw [hptc x hxK, map_smul, hptF x hxK]
  have h1 := hptc y hyK
  rw [hzero, map_smul, hptF y hyK] at h1
  -- h1 : q x • g y = q y • g y
  have hg : o.generator y ≠ 0 := o.nonzero y
  exact (smul_left_injective ℚ hg h1).symm


open TernaryPoly.RationalManifoldCompact in
/-- **Top homology of a connected compact oriented manifold is spanned by the fundamental class.** -/
theorem top_homology_eq_smul_fundamental [CompactSpace X] [PreconnectedSpace X]
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)
    (c : (supportChains (Set.univ : Set X)).homology (n+2)) :
    ∃ q : ℚ, c = q • compactFundamentalClass n e o Set.univ isCompact_univ := by
  set F := compactFundamentalClass n e o Set.univ isCompact_univ with hFdef
  have hF : ∀ (x : X) (hx : x ∈ (Set.univ : Set X)),
      homologyMap (supportPointMap Set.univ x hx) (n+2) F = o.generator x :=
    compactFundamentalClass_at_point n e o Set.univ isCompact_univ
  have hloc : ∀ x : X, ∃ q : ℚ, homologyMap (supportPointMap Set.univ x trivial) (n+2) c =
      q • o.generator x := fun x => local_top_scalar n e x (o.generator x) _ (o.nonzero x)
  choose q hq using hloc
  have hlc : IsLocallyConstant q := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    obtain ⟨V, hV, hxV, hVq⟩ := exists_nbhd_scalar_eq n e o F c hF q (fun x _ => hq x) x
    exact ⟨V, hV, hxV, hVq⟩
  by_cases hne : Nonempty X
  · obtain ⟨x₀⟩ := hne
    refine ⟨q x₀, ?_⟩
    apply manifold_compact_detect n e Set.univ isCompact_univ
    intro y hy
    rw [map_smul, hF y hy, hq y]
    rw [hlc.apply_eq_of_isPreconnected isPreconnected_univ (Set.mem_univ y) (Set.mem_univ x₀)]
  · have : IsEmpty X := not_nonempty_iff.mp hne
    refine ⟨0, ?_⟩
    apply manifold_compact_detect n e Set.univ isCompact_univ
    intro y
    exact isEmptyElim y


open TernaryPoly.RationalManifoldCompact TernaryPoly.HalfSpaceBoundaryOrientation
  TernaryPoly.ContractibleSingularHomology in
/-- **Absolute form.** Every class of `H_{n+2}(chains X)` of a connected compact oriented manifold is a
rational multiple of `ordinaryFundamentalClass`. -/
theorem chains_top_homology_eq_smul [CompactSpace X] [PreconnectedSpace X]
    (e : H ≃ₜ EuclideanSpace ℝ (Fin (n+2))) (o : Orientation (n+2) X)
    (c : (chains X).homology (n+2)) :
    ∃ q : ℚ, c = q • ordinaryFundamentalClass n e o := by
  obtain ⟨q, hq⟩ := top_homology_eq_smul_fundamental n e o ((absoluteSupportHomologyIso (n+2)).hom c)
  refine ⟨q, ?_⟩
  have h1 : (absoluteSupportHomologyIso (n+2)).toLinearEquiv c =
      q • compactFundamentalClass n e o Set.univ isCompact_univ := hq
  calc c = (absoluteSupportHomologyIso (n+2)).toLinearEquiv.symm
        ((absoluteSupportHomologyIso (n+2)).toLinearEquiv c) := by simp
    _ = (absoluteSupportHomologyIso (n+2)).toLinearEquiv.symm
        (q • compactFundamentalClass n e o Set.univ isCompact_univ) := by rw [h1]
    _ = q • ordinaryFundamentalClass n e o := by
        rw [map_smul]
        rfl

end TernaryPeriodPolynomials.Argument.TopHomology
