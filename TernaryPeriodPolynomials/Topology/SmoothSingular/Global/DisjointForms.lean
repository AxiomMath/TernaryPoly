module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.DisjointCoefficients

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set CategoryTheory TopologicalSpace
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCovering SymmetricSpaceCharts
namespace DisjointQuotientCover
variable {V : Set OrbitSpace} {ι : Type} (U : DisjointQuotientCover V ι)
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F)

/-- Actual smooth-form restrictions to all disjoint quotient components. -/
def restrictForms (n : ℕ) : EquivariantForm ρ V n →ₗ[ℝ]
    (∀ i, EquivariantForm ρ (U.domain i) n) where
  toFun w i := restrictEquivariant ρ (U.subset i) n w
  map_add' w z := funext fun i => map_add (restrictEquivariant ρ (U.subset i) n) w z
  map_smul' a w := funext fun i => map_smul (restrictEquivariant ρ (U.subset i) n) a w

/-- Every actual form family on the disjoint quotient opens is compatible. -/
theorem forms_compatible (n : ℕ) (w : ∀ i, EquivariantForm ρ (U.domain i) n) :
    (formPresheaf ρ n).IsCompatible U.opens w := by
  intro i j
  by_cases hij : i = j
  · subst j
    rfl
  · apply Subtype.ext
    apply Form.ext
    intro x hx
    exact False.elim ((U.disjoint hij).le_bot ⟨hx.2.1,hx.2.2⟩)

/-- The genuine form sheaf glues the disjoint family on the original covered open. -/
def extendForms (n : ℕ) (w : ∀ i, EquivariantForm ρ (U.domain i) n) : EquivariantForm ρ V n :=
  restrictEquivariant ρ U.subset_iSup n (gluedForm ρ U.opens n w (U.forms_compatible ρ n w))

/-- The actual disjoint extension agrees with each prescribed actual local form. -/
theorem extendForms_value (n : ℕ) (w : ∀ i, EquivariantForm ρ (U.domain i) n)
    (i : ι) {x : Coordinates} (hx : x ∈ liftedDomain (U.domain i)) :
    ((U.extendForms ρ n w).val : RawForm Coordinates F n) x = ((w i).val : RawForm Coordinates F n) x := by
  rw [extendForms,restrictEquivariant_apply ρ U.subset_iSup _
    (liftedDomain_mono (U.subset i) hx)]
  exact gluedRaw_apply ρ U.opens n w (U.forms_compatible ρ n w) i hx

/-- Actual smooth forms are uniquely determined by their disjoint restrictions. -/
theorem restrictForms_injective (n : ℕ) : Function.Injective (U.restrictForms ρ n) := by
  intro w z h
  apply Subtype.ext
  apply Form.ext
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp (U.covers hx.2)
  have he := congrArg (fun c : EquivariantForm ρ (U.domain i) n =>
    (c.val : RawForm Coordinates F n) x) (congrFun h i)
  change ((restrictEquivariant ρ (U.subset i) n w).val : RawForm Coordinates F n) x =
    ((restrictEquivariant ρ (U.subset i) n z).val : RawForm Coordinates F n) x at he
  simpa only [restrictEquivariant_apply ρ (U.subset i) w ⟨hx.1,hi⟩,
    restrictEquivariant_apply ρ (U.subset i) z ⟨hx.1,hi⟩] using he

/-- Restricting the actual glued family returns the original disjoint forms. -/
theorem restrict_extendForms (n : ℕ) (w : ∀ i, EquivariantForm ρ (U.domain i) n) :
    U.restrictForms ρ n (U.extendForms ρ n w) = w := by
  funext i
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ (U.subset i) n (U.extendForms ρ n w)).val : RawForm Coordinates F n) x = _
  rw [restrictEquivariant_apply ρ (U.subset i) _ hx]
  exact U.extendForms_value ρ n w i hx

/-- The true smooth-form section space is the product of its actual disjoint component spaces. -/
def formEquiv (n : ℕ) : EquivariantForm ρ V n ≃ₗ[ℝ] (∀ i, EquivariantForm ρ (U.domain i) n) :=
  LinearEquiv.ofBijective (U.restrictForms ρ n)
    ⟨U.restrictForms_injective ρ n,fun w => ⟨U.extendForms ρ n w,U.restrict_extendForms ρ n w⟩⟩

/-- The literal disjoint form equivalence commutes with the actual exterior derivative. -/
theorem formEquiv_d (hV : IsOpen V) (n : ℕ) (w : EquivariantForm ρ V n) :
    U.formEquiv ρ (n+1) (differential ρ hV n w) =
      fun i => differential ρ (U.isOpen_domain i) n (U.formEquiv ρ n w i) := by
  funext i
  exact restrictEquivariant_d ρ hV (U.isOpen_domain i) (U.subset i) w

end DisjointQuotientCover
end TernaryPoly.SmoothSingularGlobal
