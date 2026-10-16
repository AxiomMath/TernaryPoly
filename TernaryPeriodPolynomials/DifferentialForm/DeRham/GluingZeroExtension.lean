module

public import TernaryPeriodPolynomials.DifferentialForm.DeRham.GluingExtension

@[expose] public section

noncomputable section
namespace TernaryPoly.SmoothDeRhamGluing
open Set Filter ContinuousAlternatingMap SmoothLocalDeRham SmoothCoveringDeRham
  SymmetricSpaceCharts SymmetricSpaceCovering
open scoped ContDiff Topology
open CategoryTheory

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ρ : Representation ℝ DeckGroup F} {U V W : Set OrbitSpace} {n : ℕ}

/-- Support-controlled zero extension commutes with the literal exterior derivative. -/
theorem compactZeroExtend_d (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (w : CompactSupportForm ρ U n) :
    compactDifferential ρ hV n (compactZeroExtend hU hUV n w) =
      compactZeroExtend hU hUV (n + 1) (compactDifferential ρ hU n w) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  change (d (liftedDomain_isOpen hV) n (compactZeroExtend hU hUV n w).val.val :
    RawForm Coordinates F (n + 1)) x = (d (liftedDomain_isOpen hU) n w.val.val : RawForm Coordinates F (n + 1)) x
  rw [d_apply (liftedDomain_isOpen hV) _ hx]
  change extDeriv (w.val.val : RawForm Coordinates F n) x = _
  by_cases hxU : x ∈ liftedDomain U
  · rw [d_apply (liftedDomain_isOpen hU) _ hxU]
  · rw [Form.outside (d (liftedDomain_isOpen hU) n w.val.val) hxU]
    have he := raw_eventually_zero w.val hx.1 (fun h => hxU ⟨hx.1, w.property.2 h⟩)
    rw [he.extDeriv_eq]
    simp only [extDeriv, fderiv_zero]
    exact map_zero (alternatizeUncurryFinCLM ℝ Coordinates F (n := n))

/-- Actual cochain map extending compactly supported forms by zero. -/
def compactExtensionChainMap (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) :
    compactCoveringComplex ρ hU ⟶ compactCoveringComplex ρ hV :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (compactZeroExtend hU hUV n)) (by
    intro n
    simp only [compactCoveringComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro w
    exact compactZeroExtend_d hU hV hUV w)

theorem compactZeroExtend_trans (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) (hVW : V ⊆ W)
    (w : CompactSupportForm ρ U n) :
    compactZeroExtend hV hVW n (compactZeroExtend hU hUV n w) =
      compactZeroExtend hU (hUV.trans hVW) n w := by
  apply Subtype.ext
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rfl

/-- Restricting an actual zero extension gives back the original ordinary form. -/
theorem restrict_compactZeroExtend (hU : IsOpen U) (hUV : U ⊆ V)
    (w : CompactSupportForm ρ U n) :
    restrictEquivariant ρ hUV n (compactZeroExtend hU hUV n w).val = w.val := by
  apply Subtype.ext
  apply Form.ext
  intro x hx
  rw [restrictEquivariant_apply ρ hUV _ hx, compactZeroExtend_apply]

/-- The compact-to-ordinary inclusion is compatible with extending and then restricting. -/
theorem compactInclusion_extension_restriction (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V) :
    compactExtensionChainMap (ρ := ρ) hU hV hUV ≫ compactInclusion ρ hV ≫
      restrictionChainMap ρ hV hU hUV = compactInclusion ρ hU := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact restrict_compactZeroExtend hU hUV w

end TernaryPoly.SmoothDeRhamGluing
