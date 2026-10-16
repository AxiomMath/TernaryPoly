module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Comparison.Local

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularComparison
open CategoryTheory HomologicalComplex Set SmoothLocalDeRham SmoothCoveringDeRham
open scoped ContDiff Topology
variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {s : Set D} {t : Set E}

/-- The actual differential-form pullback along a smooth map of open chart domains. -/
def deRhamPullbackForm (hs : IsOpen s) (g : D → E) (hg : ContDiffOn ℝ ∞ g s)
    (hgt : MapsTo g s t) (n : ℕ) : Form (F := F) t n →ₗ[ℝ] Form (F := F) s n where
  toFun w := restrictForm s (pullRaw g w) (pullRaw_smooth hs hg (Form.smooth w) hgt)
  map_add' w z := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, AddMemClass.coe_add, Pi.add_apply]
    ext v
    rfl
  map_smul' r w := by
    apply Form.ext
    intro x hx
    simp only [restrictForm_apply _ _ hx, SetLike.val_smul, Pi.smul_apply]
    ext v
    rfl

/-- Evaluation of the actual pullback on its open domain. -/
theorem deRhamPullbackForm_apply (hs : IsOpen s) (g : D → E) (hg : ContDiffOn ℝ ∞ g s)
    (hgt : MapsTo g s t) (n : ℕ) (w : Form (F := F) t n) {x : D} (hx : x ∈ s) :
    (deRhamPullbackForm hs g hg hgt n w : RawForm D F n) x = pullRaw g w x :=
  restrictForm_apply (pullRaw g (w : RawForm E F n))
    (pullRaw_smooth hs hg (Form.smooth w) hgt) hx

/-- Smooth coordinate pullback commutes with the literal exterior derivative. -/
theorem deRhamPullbackForm_d (hs : IsOpen s) (ht : IsOpen t) (g : D → E)
    (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) (n : ℕ) (w : Form (F := F) t n) :
    deRhamPullbackForm hs g hg hgt (n+1) (d ht n w) =
      d hs n (deRhamPullbackForm hs g hg hgt n w) := by
  apply Form.ext
  intro x hx
  rw [d_apply hs _ hx]
  have he : (deRhamPullbackForm hs g hg hgt n w : RawForm D F n) =ᶠ[𝓝 x] pullRaw g w := by
    filter_upwards [hs.mem_nhds hx] with y hy
    exact deRhamPullbackForm_apply hs g hg hgt n w hy
  rw [deRhamPullbackForm_apply hs g hg hgt (n+1) _ hx, he.extDeriv_eq,
    extDeriv_pullRaw (hg.contDiffAt (hs.mem_nhds hx))
      (((Form.smooth w).contDiffAt (ht.mem_nhds (hgt hx))).differentiableAt (by simp))]
  unfold pullRaw
  rw [d_apply ht w (hgt hx)]

/-- Actual smooth coordinate pullback as a morphism of real cochain complexes. -/
def deRhamPullback (hs : IsOpen s) (ht : IsOpen t) (g : D → E)
    (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) :
    complex (F := F) ht ⟶ complex (F := F) hs :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (deRhamPullbackForm hs g hg hgt n)) (fun n => by
    rw [deRham_d, deRham_d]
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun w => (deRhamPullbackForm_d hs ht g hg hgt n w).symm))

/-- Pullback preserves the actual constant zero-form with the same coefficient value. -/
theorem deRhamPullback_constant (hs : IsOpen s) (g : D → E)
    (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) (c : F) :
    deRhamPullbackForm hs g hg hgt 0 (deRhamConstant t c) = deRhamConstant s c := by
  apply Form.ext
  intro x hx
  rw [deRhamPullbackForm_apply hs g hg hgt 0 _ hx]
  change pullRaw g (constant t c : RawForm E F 0) x = (constant s c : RawForm D F 0) x
  unfold pullRaw
  simp only [constant, ofFunction_apply _ _ hx, ofFunction_apply _ _ (hgt hx)]
  ext v
  rfl

/-- Actual smooth coordinate pullback commutes with the common constant augmentation. -/
theorem deRhamAugmentation_pullback (hs : IsOpen s) (ht : IsOpen t) (g : D → E)
    (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) :
    deRhamAugmentation (F := F) ht ≫ deRhamPullback hs ht g hg hgt =
      deRhamAugmentation (F := F) hs := by
  apply (CochainComplex.fromSingle₀Equiv (complex (F := F) hs) (ModuleCat.of ℝ F)).injective
  apply Subtype.ext
  change ModuleCat.ofHom (deRhamConstant (F := F) t) ≫
    ModuleCat.ofHom (deRhamPullbackForm hs g hg hgt 0) = ModuleCat.ofHom (deRhamConstant (F := F) s)
  apply ModuleCat.hom_ext
  exact LinearMap.ext (deRhamPullback_constant hs g hg hgt)

/-- The actual continuous map of chart domains underlying smooth pullback. -/
def chartMap (g : D → E) (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) :
    TopCat.of s ⟶ TopCat.of t :=
  TopCat.ofHom ⟨fun x => ⟨g x, hgt x.property⟩,
    hg.continuousOn.domRestrict.subtype_mk _⟩

variable [FiniteDimensional ℝ E] [CompleteSpace F]

/-- The canonical local de Rham/singular comparison is natural for genuine smooth maps
between nonempty convex charts. Together with coefficient naturality this covers deck transitions. -/
theorem localComparison_pullback (hs : IsOpen s) (ht : IsOpen t)
    (hcs : Convex ℝ s) (hct : Convex ℝ t) (hns : s.Nonempty) (hnt : t.Nonempty)
    (g : D → E) (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) (n : ℕ) :
    (localComparison (F := F) ht hct hnt n).hom ≫
        homologyMap (singularPullback (chartMap g hg hgt) (ModuleCat.of ℝ F)) n =
      homologyMap (deRhamPullback hs ht g hg hgt) n ≫ (localComparison hs hcs hns n).hom := by
  let : ContractibleSpace (TopCat.of s) := hcs.contractibleSpace hns
  let : ContractibleSpace (TopCat.of t) := hct.contractibleSpace hnt
  let : QuasiIso (deRhamAugmentation (F := F) hs) := deRhamAugmentation_quasiIso hs hcs hns
  let : QuasiIso (deRhamAugmentation (F := F) ht) := deRhamAugmentation_quasiIso ht hct hnt
  let : QuasiIso (singularAugmentation (TopCat.of s) (ModuleCat.of ℝ F)) := singularAugmentation_quasiIso _ _
  let : QuasiIso (singularAugmentation (TopCat.of t) (ModuleCat.of ℝ F)) := singularAugmentation_quasiIso _ _
  exact comparison_natural _ _ _ _ (𝟙 _) (deRhamPullback hs ht g hg hgt)
    (singularPullback (chartMap g hg hgt) (ModuleCat.of ℝ F))
    (by simpa using deRhamAugmentation_pullback (F := F) hs ht g hg hgt)
    (by simpa using singularAugmentation_pullback (chartMap g hg hgt) (ModuleCat.of ℝ F)) n

variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Actual simultaneous coordinate and coefficient transport, in the order used by the
covering local system, commutes with the canonical local comparison. -/
theorem localComparison_twisted_pullback (hs : IsOpen s) (ht : IsOpen t)
    (hcs : Convex ℝ s) (hct : Convex ℝ t) (hns : s.Nonempty) (hnt : t.Nonempty)
    (g : D → E) (hg : ContDiffOn ℝ ∞ g s) (hgt : MapsTo g s t) (L : F →L[ℝ] G) (n : ℕ) :
    (localComparison (F := F) ht hct hnt n).hom ≫
      homologyMap (singularPullback (chartMap g hg hgt) (ModuleCat.of ℝ F)) n ≫
        homologyMap (realHomCoefficient (realSingularChains (TopCat.of s))
          (ModuleCat.ofHom L.toLinearMap)) n =
    homologyMap (deRhamPullback (F := F) hs ht g hg hgt) n ≫
      homologyMap (deRhamCoefficient L hs) n ≫ (localComparison hs hcs hns n).hom := by
  rw [← Category.assoc, localComparison_pullback hs ht hcs hct hns hnt g hg hgt n,
    Category.assoc, localComparison_coefficient L hs hcs hns n]

end TernaryPoly.SmoothSingularComparison
