module

public import TernaryPeriodPolynomials.Topology.SmoothSingular.Global.CechExactness

@[expose] public section


noncomputable section
namespace TernaryPoly.SmoothSingularGlobal
open Set Function CategoryTheory
open SmoothLocalDeRham SmoothCoveringDeRham SymmetricSpaceCharts SymmetricSpaceCovering
open scoped Topology ContDiff Manifold
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  (ρ : Representation ℝ DeckGroup F) {ι : Type*} (U : ι → Set OrbitSpace) (n : ℕ)

/-- The actual empty Čech domain contains the whole quotient. -/
theorem univ_subset_cechDomain_empty (t : Fin 0 → ι) : Set.univ ⊆ cechDomain U t := by
  rw [cechDomain_empty]

/-- The actual global form restricts to the augmented empty Čech intersection. -/
def formCechEmptyEmbed : EquivariantForm ρ Set.univ n →ₗ[ℝ] FormCechTerms ρ U n 0 :=
  LinearMap.pi (fun _ => restrictEquivariant ρ (Set.subset_univ _) n)

/-- Recover the genuine global form from its empty Čech component. -/
def formCechEmptyRecover : FormCechTerms ρ U n 0 →ₗ[ℝ] EquivariantForm ρ Set.univ n :=
  (restrictEquivariant ρ (univ_subset_cechDomain_empty U Fin.elim0) n).comp
    (LinearMap.proj Fin.elim0)

/-- The genuine empty Čech embedding followed by recovery is the identity. -/
theorem formCechEmptyRecover_embed (w : EquivariantForm ρ Set.univ n) :
    formCechEmptyRecover ρ U n (formCechEmptyEmbed ρ U n w) = w := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ (univ_subset_cechDomain_empty U Fin.elim0) n
    (restrictEquivariant ρ (Set.subset_univ _) n w)).val : RawForm Coordinates F n) x = _
  rw [restrictEquivariant_apply ρ _ _ hx,
    restrictEquivariant_apply ρ _ _ (liftedDomain_mono (univ_subset_cechDomain_empty U Fin.elim0) hx)]

/-- All actual empty Čech components agree, so global recovery followed by embedding is identity. -/
theorem formCechEmptyEmbed_recover (w : FormCechTerms ρ U n 0) :
    formCechEmptyEmbed ρ U n (formCechEmptyRecover ρ U n w) = w := by
  funext t
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change ((restrictEquivariant ρ (Set.subset_univ _) n
    (restrictEquivariant ρ (univ_subset_cechDomain_empty U Fin.elim0) n (w Fin.elim0))).val :
      RawForm Coordinates F n) x = _
  rw [restrictEquivariant_apply ρ _ _ hx,
    restrictEquivariant_apply ρ _ _ (liftedDomain_mono (Set.subset_univ _) hx)]
  exact congrArg (fun s => ((w s).val : RawForm Coordinates F n) x) (Subsingleton.elim _ t)

/-- The augmented empty Čech term is the genuine global equivariant-form space. -/
def formCechEmptyEquiv : EquivariantForm ρ Set.univ n ≃ₗ[ℝ] FormCechTerms ρ U n 0 :=
  { formCechEmptyEmbed ρ U n with
    invFun := formCechEmptyRecover ρ U n
    left_inv := formCechEmptyRecover_embed ρ U n
    right_inv := formCechEmptyEmbed_recover ρ U n }

end TernaryPoly.SmoothSingularGlobal
