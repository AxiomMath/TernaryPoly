module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.Coefficient

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set
open SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Topology Classical
variable {F : Type} [AddCommGroup F] [Module ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Opens (TopCat.of OrbitSpace))
  (w : ∀ i, coefficientSections ρ (U i : Set OrbitSpace))

/-- Compatibility of coefficient restrictions is literal equality on overlaps. -/
theorem coefficientCompatible_apply (hw : (coefficientPresheaf ρ).IsCompatible U w)
    (i j : ι) (x : Coordinates) (hi : x ∈ liftedDomain (U i : Set OrbitSpace))
    (hj : x ∈ liftedDomain (U j : Set OrbitSpace)) :
    (w i).val ⟨x, hi⟩ = (w j).val ⟨x, hj⟩ := by
  exact congrArg (fun z : coefficientSections ρ
    ((U i ⊓ U j : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) =>
      z.val ⟨x, hi.1, hi.2, hj.2⟩) (hw i j)

/-- The actual compatible local values give a coefficient function on the lifted union. -/
def gluedCoefficientFun (x : CoverOpen (iSup U : Opens (TopCat.of OrbitSpace))) : F :=
  let h := (mem_lifted_iSup U).mp x.property
  (w h.choose).val ⟨x.val, h.choose_spec⟩

/-- The glued function agrees literally with each local coefficient function. -/
theorem gluedCoefficientFun_apply (hw : (coefficientPresheaf ρ).IsCompatible U w)
    (i : ι) (x : CoverOpen (iSup U : Opens (TopCat.of OrbitSpace)))
    (hi : x.val ∈ liftedDomain (U i : Set OrbitSpace)) :
    gluedCoefficientFun ρ U w x = (w i).val ⟨x.val, hi⟩ := by
  exact coefficientCompatible_apply ρ U w hw _ i x.val _ hi

/-- Lifted quotient-open inclusions are genuinely open maps. -/
theorem coverInclusion_isOpenMap {U V : Set OrbitSpace} (hVU : V ⊆ U) (hV : IsOpen V) :
    IsOpenMap (coverInclusion hVU) :=
  (liftedDomain_isOpen hV).isOpenMap_inclusion (liftedDomain_mono hVU)

/-- The glued coefficient function is locally constant, proved using open local fibers. -/
theorem gluedCoefficientFun_locallyConstant (hw : (coefficientPresheaf ρ).IsCompatible U w) :
    IsLocallyConstant (gluedCoefficientFun ρ U w) := by
  intro A
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp x.property
  let hU : (U i : Set OrbitSpace) ⊆
      ((iSup U : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) :=
    fun _ hy => Opens.mem_iSup.mpr ⟨i, hy⟩
  let B : Set (CoverOpen (U i : Set OrbitSpace)) := (w i).val ⁻¹' A
  refine ⟨coverInclusion hU '' B, ?_, ?_, ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    change gluedCoefficientFun ρ U w (coverInclusion hU z) ∈ A
    rw [gluedCoefficientFun_apply ρ U w hw i _ z.property]
    exact hz
  · exact coverInclusion_isOpenMap hU (U i).isOpen B ((w i).val.isLocallyConstant A)
  · refine ⟨⟨x.val, hi⟩, ?_, rfl⟩
    change (w i).val ⟨x.val, hi⟩ ∈ A
    rw [← gluedCoefficientFun_apply ρ U w hw i x hi]
    exact hx

/-- Genuine locally constant equivariant coefficient sections glue over arbitrary quotient covers. -/
def gluedCoefficient (hw : (coefficientPresheaf ρ).IsCompatible U w) :
    coefficientSections ρ (iSup U : Opens (TopCat.of OrbitSpace)) :=
  ⟨⟨gluedCoefficientFun ρ U w, gluedCoefficientFun_locallyConstant ρ U w hw⟩, by
    intro g x
    obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp x.property
    change gluedCoefficientFun ρ U w (g • x) = ρ g (gluedCoefficientFun ρ U w x)
    rw [gluedCoefficientFun_apply ρ U w hw i _ (deckMap_liftedDomain g _ hi),
      gluedCoefficientFun_apply ρ U w hw i _ hi]
    exact (w i).property g ⟨x.val, hi⟩⟩

/-- The glued actual coefficient section has the required restrictions. -/
theorem gluedCoefficient_restrict (hw : (coefficientPresheaf ρ).IsCompatible U w) (i : ι) :
    (coefficientPresheaf ρ).map (Opens.leSupr U i).op (gluedCoefficient ρ U w hw) = w i := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  exact gluedCoefficientFun_apply ρ U w hw i _ x.property

/-- Actual coefficient gluing is unique. -/
theorem gluedCoefficient_unique (hw : (coefficientPresheaf ρ).IsCompatible U w)
    (z : coefficientSections ρ (iSup U : Opens (TopCat.of OrbitSpace)))
    (hz : (coefficientPresheaf ρ).IsGluing U w z) : z = gluedCoefficient ρ U w hw := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp x.property
  have he := congrArg (fun a : coefficientSections ρ (U i : Set OrbitSpace) =>
    a.val ⟨x.val, hi⟩) (hz i)
  exact he.trans (gluedCoefficientFun_apply ρ U w hw i x hi).symm

/-- The actual real locally constant equivariant coefficient presheaf is a sheaf. -/
theorem coefficientPresheaf_isSheaf : (coefficientPresheaf ρ).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U w hw
  exact ⟨gluedCoefficient ρ U w hw, gluedCoefficient_restrict ρ U w hw,
    fun z hz => gluedCoefficient_unique ρ U w hw z hz⟩

/-- The genuine sheaf of locally constant equivariant coefficients on the arithmetic quotient. -/
def coefficientSheaf : (TopCat.of OrbitSpace).Sheaf (ModuleCat ℝ) :=
  ⟨coefficientPresheaf ρ, coefficientPresheaf_isSheaf ρ⟩

end TernaryPoly.SmoothSingularGlobal
