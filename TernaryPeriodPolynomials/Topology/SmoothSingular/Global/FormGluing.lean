module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FormPresheaf

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open CategoryTheory Opposite TopologicalSpace Set Filter
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
open scoped Topology ContDiff Classical
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type} (U : ι → Opens (TopCat.of OrbitSpace)) (n : ℕ)
  (w : ∀ i, EquivariantForm ρ (U i : Set OrbitSpace) n)

/-- A point of the lifted union belongs to one of the actual lifted quotient opens. -/
theorem mem_lifted_iSup {x : Coordinates} :
    x ∈ liftedDomain (iSup U : Opens (TopCat.of OrbitSpace)) ↔
      ∃ i, x ∈ liftedDomain (U i : Set OrbitSpace) := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx.2
    exact ⟨i, hx.1, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨hi.1, Opens.mem_iSup.mpr ⟨i, hi.2⟩⟩

/-- Compatible actual restrictions give literal equality of raw form values on each overlap. -/
theorem formCompatible_apply (hw : (formPresheaf ρ n).IsCompatible U w)
    (i j : ι) {x : Coordinates} (hi : x ∈ liftedDomain (U i : Set OrbitSpace))
    (hj : x ∈ liftedDomain (U j : Set OrbitSpace)) :
    ((w i).val : RawForm Coordinates F n) x = ((w j).val : RawForm Coordinates F n) x := by
  have hx : x ∈ liftedDomain ((U i ⊓ U j : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) :=
    ⟨hi.1, hi.2, hj.2⟩
  have h := congrArg (fun z : EquivariantForm ρ
      ((U i ⊓ U j : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) n =>
        (z.val : RawForm Coordinates F n) x) (hw i j)
  change ((restrictEquivariant ρ (show ((U i ⊓ U j : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) ⊆ U i from fun _ h => h.1)
      n (w i)).val : RawForm Coordinates F n) x =
    ((restrictEquivariant ρ (show ((U i ⊓ U j : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace) ⊆ U j from fun _ h => h.2)
      n (w j)).val : RawForm Coordinates F n) x at h
  rw [restrictEquivariant_apply ρ _ _ hx, restrictEquivariant_apply ρ _ _ hx] at h
  exact h

/-- The glued raw representative is the compatible local value, and is zero outside the union. -/
def gluedRaw : RawForm Coordinates F n := fun x =>
  if h : ∃ i, x ∈ liftedDomain (U i : Set OrbitSpace) then ((w h.choose).val : RawForm Coordinates F n) x else 0

/-- On each covering open, the glued representative has exactly the given raw value. -/
theorem gluedRaw_apply (hw : (formPresheaf ρ n).IsCompatible U w)
    (i : ι) {x : Coordinates} (hi : x ∈ liftedDomain (U i : Set OrbitSpace)) :
    gluedRaw ρ U n w x = ((w i).val : RawForm Coordinates F n) x := by
  have hx : ∃ j, x ∈ liftedDomain (U j : Set OrbitSpace) := ⟨i, hi⟩
  rw [gluedRaw, dite_eq_left hx]
  exact formCompatible_apply ρ U n w hw hx.choose i hx.choose_spec hi

/-- Smoothness of the actual glued raw form follows locally from the given smooth forms. -/
theorem gluedRaw_smooth (hw : (formPresheaf ρ n).IsCompatible U w) :
    ContDiffOn ℝ ∞ (gluedRaw ρ U n w) (liftedDomain (iSup U : Opens (TopCat.of OrbitSpace))) := by
  intro x hx
  obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp hx
  have he : gluedRaw ρ U n w =ᶠ[𝓝 x] ((w i).val : RawForm Coordinates F n) := by
    filter_upwards [(liftedDomain_isOpen (U i).isOpen).mem_nhds hi] with y hy
    exact gluedRaw_apply ρ U n w hw i hy
  exact (((Form.smooth (w i).val).contDiffAt
    ((liftedDomain_isOpen (U i).isOpen).mem_nhds hi)).congr_of_eventuallyEq he).contDiffWithinAt

/-- The actual glued smooth equivariant form, not just a gluing in an ambient function sheaf. -/
def gluedForm (hw : (formPresheaf ρ n).IsCompatible U w) :
    EquivariantForm ρ (iSup U : Opens (TopCat.of OrbitSpace)) n :=
  ⟨⟨gluedRaw ρ U n w, gluedRaw_smooth ρ U n w hw, by
      intro x hx
      have hn : ¬ ∃ i, x ∈ liftedDomain (U i : Set OrbitSpace) := by
        exact fun h => hx ((mem_lifted_iSup U).mpr h)
      simp only [gluedRaw, dite_eq_right hn]⟩, by
    intro g x hx
    obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp hx
    change (gluedRaw ρ U n w (deckMap g x)).compContinuousLinearMap (fderiv ℝ (deckMap g) x) =
      coefficientFormMap (coefficientMap ρ g) n (gluedRaw ρ U n w x)
    rw [gluedRaw_apply ρ U n w hw i (deckMap_liftedDomain g _ hi), gluedRaw_apply ρ U n w hw i hi]
    exact (w i).property g x hi⟩

/-- The glued equivariant form restricts to every given local form. -/
theorem gluedForm_restrict (hw : (formPresheaf ρ n).IsCompatible U w) (i : ι) :
    restrictEquivariant ρ (show (U i : Set OrbitSpace) ⊆ ((iSup U : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace)
      from fun _ hx => Opens.mem_iSup.mpr ⟨i, hx⟩) n
      (gluedForm ρ U n w hw) = w i := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [restrictEquivariant_apply ρ _ _ hx]
  exact gluedRaw_apply ρ U n w hw i hx

/-- The actual glued form is the unique form with the prescribed local restrictions. -/
theorem gluedForm_unique (hw : (formPresheaf ρ n).IsCompatible U w)
    (z : EquivariantForm ρ (iSup U : Opens (TopCat.of OrbitSpace)) n)
    (hz : ∀ i, restrictEquivariant ρ (show (U i : Set OrbitSpace) ⊆ ((iSup U : Opens (TopCat.of OrbitSpace)) : Set OrbitSpace)
      from fun _ hx => Opens.mem_iSup.mpr ⟨i, hx⟩) n z = w i) :
    z = gluedForm ρ U n w hw := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  obtain ⟨i, hi⟩ := (mem_lifted_iSup U).mp hx
  have he := congrArg (fun a : EquivariantForm ρ (U i : Set OrbitSpace) n =>
    (a.val : RawForm Coordinates F n) x) (hz i)
  rw [restrictEquivariant_apply ρ _ _ hi] at he
  exact he.trans (gluedRaw_apply ρ U n w hw i hi).symm

end TernaryPoly.SmoothSingularGlobal
