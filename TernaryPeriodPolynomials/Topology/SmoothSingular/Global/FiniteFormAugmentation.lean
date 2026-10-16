module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.FiniteFormCech
public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechAugmentation
public import TernaryPeriodPolynomials.DifferentialForm.DeRham.Covering.CompactSupport

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- A genuinely nonzero equivariant form has a nonzero covering value on its actual domain. -/
theorem equivariantForm_exists_ne_zero {U : Set OrbitSpace} {n : ℕ}
    (w : EquivariantForm ρ U n) (hw : w ≠ 0) :
    ∃ x ∈ liftedDomain U, (w.val : RawForm Coordinates F n) x ≠ 0 := by
  by_contra! h
  apply hw
  apply Subtype.ext
  apply Form.ext
  exact h

/-- The global Čech augmentation is literal restriction at every covering point. -/
theorem formCechAugmentationMap_value {ι : Type} (U : ι → Set OrbitSpace) (n : ℕ)
    (w : EquivariantForm ρ Set.univ n) (t : Fin 1 → ι)
    (x : Coordinates) (hx : x ∈ liftedDomain (cechDomain U t)) :
    (((formCechAugmentationMap ρ U n w) t).val : RawForm Coordinates F n) x =
      (w.val : RawForm Coordinates F n) x := by
  change ((formCechD ρ U n 0 (formCechEmptyEmbed ρ U n w) t).val : RawForm Coordinates F n) x = _
  rw [formCechD_zero_value ρ U n _ t x hx]
  exact restrictEquivariant_apply ρ (Set.subset_univ _) w
    (show x ∈ liftedDomain (cechDomain U Fin.elim0) by
      rw [cechDomain_empty]; exact ⟨hx.1,mem_univ _⟩)

variable (C : CompactConvexCover)

/-- A genuinely quotient-compact global form has only finitely many nonzero actual Čech
restrictions on the locally finite compact-closure cover. -/
theorem formCechAugmentationMap_finiteSupport (n : ℕ)
    (w : EquivariantForm ρ Set.univ n) (hw : HasQuotientCompactSupport ρ w) :
    (familySupport (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w)).Finite := by
  apply (C.finite_tuples_meeting 1 hw.1).subset
  intro t ht
  obtain ⟨x,hx,hxn⟩ := equivariantForm_exists_ne_zero ρ _ ht
  refine ⟨coordinateProjection x,hx.2,subset_closure ⟨x,?_,rfl⟩⟩
  rw [formCechAugmentationMap_value ρ _ n w t x hx] at hxn
  exact hxn

/-- Finite actual Čech restriction support forces genuine compact quotient support. Its
closed support lies in the finite union of the selected genuine sheet closures. -/
theorem compactSupport_of_formCechAugmentationMap_finiteSupport (n : ℕ)
    (w : EquivariantForm ρ Set.univ n)
    (hw : (familySupport (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w)).Finite) :
    HasQuotientCompactSupport ρ w := by
  let T := familySupport (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w)
  let K : Set OrbitSpace := ⋃ t ∈ T, closure (C.sheet (t 0)).quotientDomain
  have hK : IsCompact K := hw.isCompact_biUnion (fun t _ => C.compactClosure (t 0))
  have hsupport : quotientSupport w ⊆ K := by
    apply closure_minimal _ hK.isClosed
    rintro q ⟨x,hx,rfl⟩
    have hxp : x ∈ liftedDomain Set.univ := by
      by_contra hn
      exact hx (Form.outside w.val hn)
    obtain ⟨i,hi⟩ := mem_iUnion.mp
      (show coordinateProjection x ∈ ⋃ i, (C.sheet i).quotientDomain by rw [C.covers]; trivial)
    let t : Fin 1 → C.Index := fun _ => i
    have hxt : x ∈ liftedDomain (cechDomain (fun i => (C.sheet i).quotientDomain) t) :=
      ⟨hxp.1,mem_iInter.mpr (fun _ => hi)⟩
    have ht : t ∈ T := by
      intro hz
      have hv := formCechAugmentationMap_value ρ (fun i => (C.sheet i).quotientDomain) n w t x hxt
      have hzv : (((formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w) t).val :
          RawForm Coordinates F n) x = 0 := by rw [hz]; rfl
      exact hx (hv.symm.trans hzv)
    exact mem_iUnion₂.mpr ⟨t,ht,subset_closure hi⟩
  exact ⟨hK.of_isClosed_subset isClosed_closure hsupport,subset_univ _⟩

/-- Genuine compact quotient support is exactly finite support of literal chart restrictions. -/
theorem compactSupport_iff_formCechAugmentationMap_finiteSupport (n : ℕ)
    (w : EquivariantForm ρ Set.univ n) : HasQuotientCompactSupport ρ w ↔
    (familySupport (formCechAugmentationMap ρ (fun i => (C.sheet i).quotientDomain) n w)).Finite :=
  ⟨formCechAugmentationMap_finiteSupport ρ C n w,
    compactSupport_of_formCechAugmentationMap_finiteSupport ρ C n w⟩

end TernaryPoly.SmoothSingularGlobal
