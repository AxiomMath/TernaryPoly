module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingZeroExtension

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V : Set OrbitSpace} {n : ℕ}

/-- Restrict a compactly supported form to a smaller open containing its whole actual projected
support. Its canonical raw covering function is unchanged everywhere. -/
def compactRestrictOfSupport (hVU : V ⊆ U) (w : CompactSupportForm ρ U n)
    (hwV : quotientSupport w.val ⊆ V) : CompactSupportForm ρ V n :=
  ⟨⟨⟨(w.val.val : RawForm Coordinates F n),
    (Form.smooth w.val.val).mono (liftedDomain_mono hVU), by
      intro x hx
      by_contra hn
      have hxU : x ∈ liftedDomain U := by
        by_contra h
        exact hn (Form.outside w.val.val h)
      exact hx ⟨hxU.1, hwV (subset_closure ⟨x, hn, rfl⟩)⟩⟩,
    fun g x hx => w.val.property g x (liftedDomain_mono hVU hx)⟩, w.property.1, hwV⟩

@[simp] theorem compactRestrictOfSupport_apply (hVU : V ⊆ U) (w : CompactSupportForm ρ U n)
    (hwV : quotientSupport w.val ⊆ V) (x : Coordinates) :
    ((compactRestrictOfSupport hVU w hwV).val.val : RawForm Coordinates F n) x =
      (w.val.val : RawForm Coordinates F n) x := rfl

theorem extend_compactRestrictOfSupport (hV : IsOpen V) (hVU : V ⊆ U)
    (w : CompactSupportForm ρ U n) (hwV : quotientSupport w.val ⊆ V) :
    compactZeroExtend hV hVU n (compactRestrictOfSupport hVU w hwV) = w := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rfl

/-- Genuine compact-support locality under every directed open exhaustion. Every compact form
is the actual zero extension of a form on a single stage of the exhaustion. -/
theorem compactSupport_directed_exhaustion {ι : Type*} [Nonempty ι]
    (D : ι → Set OrbitSpace) (hD : ∀ i, IsOpen (D i)) (hDU : ∀ i, D i ⊆ U)
    (hcover : U ⊆ ⋃ i, D i) (hdir : Directed (· ⊆ ·) D) (w : CompactSupportForm ρ U n) :
    ∃ i, ∃ z : CompactSupportForm ρ (D i) n, compactZeroExtend (hD i) (hDU i) n z = w := by
  obtain ⟨i, hi⟩ := w.property.1.elim_directed_cover D hD (w.property.2.trans hcover) hdir
  exact ⟨i, compactRestrictOfSupport (hDU i) w hi,
    extend_compactRestrictOfSupport (hD i) (hDU i) w hi⟩

end TernaryPoly.SmoothDeRhamGluing
