module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingWeightedExtension

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) (U V : Set OrbitSpace) (n : ℕ)

instance equivariantAddCommGroup : AddCommGroup (EquivariantForm ρ U n) :=
  Submodule.addCommGroup (R := ℝ) (M := Form (F := F) (liftedDomain U) n)
    (module_M := inferInstance) (equivariantSubmodule ρ U n)

/-- The actual first ordinary Mayer-Vietoris map, restricting to both quotient opens. -/
def unionRestriction : EquivariantForm ρ (U ∪ V) n →ₗ[ℝ]
    EquivariantForm ρ U n × EquivariantForm ρ V n :=
  (restrictEquivariant ρ subset_union_left n).prod (restrictEquivariant ρ subset_union_right n)

/-- The actual ordinary Mayer-Vietoris overlap map, with the convention left minus right. -/
def intersectionDifference : (EquivariantForm ρ U n × EquivariantForm ρ V n) →ₗ[ℝ]
    EquivariantForm ρ (U ∩ V) n :=
  (restrictEquivariant ρ (inter_subset_left : U ∩ V ⊆ U) n).comp (LinearMap.fst ℝ (EquivariantForm ρ U n) (EquivariantForm ρ V n)) -
    (restrictEquivariant ρ (inter_subset_right : U ∩ V ⊆ V) n).comp (LinearMap.snd ℝ (EquivariantForm ρ U n) (EquivariantForm ρ V n))

theorem intersectionDifference_unionRestriction (w : EquivariantForm ρ (U ∪ V) n) :
    intersectionDifference ρ U V n (unionRestriction ρ U V n w) = 0 := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ inter_subset_left n (restrictEquivariant ρ subset_union_left n w)).val :
    RawForm Coordinates F n) x - ((restrictEquivariant ρ inter_subset_right n
      (restrictEquivariant ρ subset_union_right n w)).val : RawForm Coordinates F n) x = 0
  rw [restrictEquivariant_apply ρ _ _ hx, restrictEquivariant_apply ρ _ _ hx,
    restrictEquivariant_apply ρ _ w ⟨hx.1, hx.2.1⟩,
    restrictEquivariant_apply ρ _ w ⟨hx.1, hx.2.2⟩, sub_self]

theorem unionRestriction_injective : Function.Injective (unionRestriction ρ U V n) := by
  intro w z h
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rcases hx.2 with hU | hV
  · have he := congrArg (fun p : EquivariantForm ρ U n × EquivariantForm ρ V n =>
      (p.1.val : RawForm Coordinates F n) x) h
    change ((restrictEquivariant ρ subset_union_left n w).val : RawForm Coordinates F n) x =
      ((restrictEquivariant ρ subset_union_left n z).val : RawForm Coordinates F n) x at he
    simpa only [restrictEquivariant_apply ρ _ _ ⟨hx.1, hU⟩] using he
  · have he := congrArg (fun p : EquivariantForm ρ U n × EquivariantForm ρ V n =>
      (p.2.val : RawForm Coordinates F n) x) h
    change ((restrictEquivariant ρ subset_union_right n w).val : RawForm Coordinates F n) x =
      ((restrictEquivariant ρ subset_union_right n z).val : RawForm Coordinates F n) x at he
    simpa only [restrictEquivariant_apply ρ _ _ ⟨hx.1, hV⟩] using he

/-- Surjectivity of the actual ordinary overlap map, proved with the true smooth partition. -/
theorem intersectionDifference_surjective (hU : IsOpen U) (hV : IsOpen V) :
    Function.Surjective (intersectionDifference ρ U V n) := by
  obtain ⟨φ, ψ, hφ, hψ, hsum, hφzero, hψzero⟩ := exists_two_local_cutoffs hU hV
  intro w
  have hψU := hψ.mono (subset_union_left : U ⊆ U ∪ V)
  have hφV := hφ.mono (subset_union_right : V ⊆ U ∪ V)
  have hzU : ∀ q ∈ U, q ∉ U ∩ V → ψ =ᶠ[𝓝 q] 0 := by
    intro q hq hn
    exact hψzero q (Or.inl hq) (fun h => hn ⟨hq, h⟩)
  have hzV : ∀ q ∈ V, q ∉ U ∩ V → φ =ᶠ[𝓝 q] 0 := by
    intro q hq hn
    exact hφzero q (Or.inr hq) (fun h => hn ⟨h, hq⟩)
  let a := weightedExtend (hU.inter hV) hU inter_subset_left ψ hψU hzU n w
  let b := weightedExtend (hU.inter hV) hV inter_subset_right φ hφV hzV n w
  refine ⟨(a, -b), ?_⟩
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ inter_subset_left n a).val : RawForm Coordinates F n) x -
    ((restrictEquivariant ρ inter_subset_right n (-b)).val : RawForm Coordinates F n) x = _
  rw [restrictEquivariant_apply ρ _ a hx, restrictEquivariant_apply ρ _ (-b) hx]
  change liftScalar ψ x • (w.val : RawForm Coordinates F n) x -
    -(liftScalar φ x • (w.val : RawForm Coordinates F n) x) = _
  rw [sub_neg_eq_add, ← add_smul]
  change (ψ (coordinateProjection x) + φ (coordinateProjection x)) • _ = _
  rw [add_comm, hsum _ (Or.inl hx.2.1), one_smul]

end TernaryPoly.SmoothDeRhamGluing
