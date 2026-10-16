module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingOrdinaryMaps

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V : Set OrbitSpace} {n : ℕ}

/-- Literal gluing of the canonical covering representatives. -/
def glueRaw (a : EquivariantForm ρ U n) (b : EquivariantForm ρ V n) : RawForm Coordinates F n := by
  classical
  exact fun x => if x ∈ liftedDomain U then (a.val : RawForm Coordinates F n) x else (b.val : RawForm Coordinates F n) x

theorem glueRaw_left (a : EquivariantForm ρ U n) (b : EquivariantForm ρ V n)
    {x : Coordinates} (hx : x ∈ liftedDomain U) :
    glueRaw a b x = (a.val : RawForm Coordinates F n) x := by simp [glueRaw, hx]

theorem glueRaw_right (a : EquivariantForm ρ U n) (b : EquivariantForm ρ V n)
    (hab : ∀ x ∈ liftedDomain (U ∩ V), (a.val : RawForm Coordinates F n) x = (b.val : RawForm Coordinates F n) x)
    {x : Coordinates} (hx : x ∈ liftedDomain V) :
    glueRaw a b x = (b.val : RawForm Coordinates F n) x := by
  by_cases hxU : x ∈ liftedDomain U
  · rw [glueRaw_left a b hxU]
    exact hab x ⟨hx.1, hxU.2, hx.2⟩
  · simp [glueRaw, hxU]

/-- Smooth equivariant forms which agree on the actual overlap glue on the actual union. -/
def glueForm (hU : IsOpen U) (hV : IsOpen V) (a : EquivariantForm ρ U n) (b : EquivariantForm ρ V n)
    (hab : ∀ x ∈ liftedDomain (U ∩ V), (a.val : RawForm Coordinates F n) x = (b.val : RawForm Coordinates F n) x) :
    EquivariantForm ρ (U ∪ V) n :=
  ⟨⟨glueRaw a b, by
    intro x hx
    rcases hx.2 with hxU | hxV
    · have he : glueRaw a b =ᶠ[𝓝 x] (a.val : RawForm Coordinates F n) := by
        filter_upwards [(liftedDomain_isOpen hU).mem_nhds ⟨hx.1, hxU⟩] with y hy using glueRaw_left a b hy
      exact (((Form.smooth a.val x ⟨hx.1, hxU⟩).contDiffAt
        ((liftedDomain_isOpen hU).mem_nhds ⟨hx.1, hxU⟩)).congr_of_eventuallyEq he).contDiffWithinAt
    · have he : glueRaw a b =ᶠ[𝓝 x] (b.val : RawForm Coordinates F n) := by
        filter_upwards [(liftedDomain_isOpen hV).mem_nhds ⟨hx.1, hxV⟩] with y hy using glueRaw_right a b hab hy
      exact (((Form.smooth b.val x ⟨hx.1, hxV⟩).contDiffAt
        ((liftedDomain_isOpen hV).mem_nhds ⟨hx.1, hxV⟩)).congr_of_eventuallyEq he).contDiffWithinAt,
    by
      intro x hx
      have hnU : x ∉ liftedDomain U := fun h => hx ⟨h.1, Or.inl h.2⟩
      have hnV : x ∉ liftedDomain V := fun h => hx ⟨h.1, Or.inr h.2⟩
      simpa only [glueRaw, ite_eq_right hnU] using Form.outside b.val hnV⟩, by
    intro g x hx
    rcases hx.2 with hxU | hxV
    · change (glueRaw a b (deckMap g x)).compContinuousLinearMap _ = coefficientFormMap _ _ (glueRaw a b x)
      rw [glueRaw_left a b (deckMap_liftedDomain g U ⟨hx.1, hxU⟩), glueRaw_left a b ⟨hx.1, hxU⟩]
      exact a.property g x ⟨hx.1, hxU⟩
    · change (glueRaw a b (deckMap g x)).compContinuousLinearMap _ = coefficientFormMap _ _ (glueRaw a b x)
      rw [glueRaw_right a b hab (deckMap_liftedDomain g V ⟨hx.1, hxV⟩), glueRaw_right a b hab ⟨hx.1, hxV⟩]
      exact b.property g x ⟨hx.1, hxV⟩⟩

theorem unionRestriction_glueForm (hU : IsOpen U) (hV : IsOpen V)
    (a : EquivariantForm ρ U n) (b : EquivariantForm ρ V n)
    (hab : ∀ x ∈ liftedDomain (U ∩ V), (a.val : RawForm Coordinates F n) x = (b.val : RawForm Coordinates F n) x) :
    unionRestriction ρ U V n (glueForm hU hV a b hab) = (a, b) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Form.ext
    intro x hx
    change ((restrictEquivariant ρ subset_union_left n (glueForm hU hV a b hab)).val : RawForm Coordinates F n) x = _
    rw [restrictEquivariant_apply ρ _ _ hx]
    exact glueRaw_left a b hx
  · apply Subtype.ext
    apply Form.ext
    intro x hx
    change ((restrictEquivariant ρ subset_union_right n (glueForm hU hV a b hab)).val : RawForm Coordinates F n) x = _
    rw [restrictEquivariant_apply ρ _ _ hx]
    exact glueRaw_right a b hab hx

/-- Exactness at the middle ordinary Mayer-Vietoris term, with the actual gluing witness. -/
theorem ordinary_kernel_exact (hU : IsOpen U) (hV : IsOpen V)
    (p : EquivariantForm ρ U n × EquivariantForm ρ V n) :
    intersectionDifference ρ U V n p = 0 ↔
      ∃ w : EquivariantForm ρ (U ∪ V) n, unionRestriction ρ U V n w = p := by
  constructor
  · intro hp
    have hab : ∀ x ∈ liftedDomain (U ∩ V),
        (p.1.val : RawForm Coordinates F n) x = (p.2.val : RawForm Coordinates F n) x := by
      intro x hx
      have he := congrArg (fun w : EquivariantForm ρ (U ∩ V) n => (w.val : RawForm Coordinates F n) x) hp
      change ((restrictEquivariant ρ inter_subset_left n p.1).val : RawForm Coordinates F n) x -
        ((restrictEquivariant ρ inter_subset_right n p.2).val : RawForm Coordinates F n) x = 0 at he
      rw [restrictEquivariant_apply ρ _ _ hx, restrictEquivariant_apply ρ _ _ hx] at he
      exact sub_eq_zero.mp he
    exact ⟨glueForm hU hV p.1 p.2 hab, unionRestriction_glueForm hU hV p.1 p.2 hab⟩
  · rintro ⟨w, rfl⟩
    exact intersectionDifference_unionRestriction ρ U V n w

end TernaryPoly.SmoothDeRhamGluing
