module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Maps

@[expose] public section


/-!
# Coefficient systems that agree on the level, and the dual transport of inner classes

Cohomology of the level only sees a coefficient system on the level itself. For two
representations `ρ₁ ρ₂` of `GL₃(ℚ)` that agree on `rationalLevel`, the cochains on any flag variety
are literally the same functions (`castCochains`, `castCocycles`), compatibly with the boundary map.

Together with the dual transport of `Dual/Maps` this gives the following: if `ρ` and `ρ ∘ φ` agree
on the level (as for the degree-zero coefficient system `det⁻¹`, whose values on the level are
`±1`), then the vanishing of the inner line classes of `ρ` implies the vanishing of the inner plane
classes of `ρ` (`innerBoundaryRep_plane_zero`).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

section Congruence

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ₁ ρ₂ : Representation ℂ RationalGL3 V)
  (h : ∀ g ∈ rationalLevel, ρ₂ g = ρ₁ g) (X : Type) [MulAction RationalGL3 X]

/-- Cochains for two coefficient systems that agree on the level are the same functions. -/
def castCochains (k : ℕ) :
    cochains rationalLevel (functionRepresentation ρ₁ X) k →ₗ[ℂ]
      cochains rationalLevel (functionRepresentation ρ₂ X) k where
  toFun f := ⟨f.val, by
    intro γ x
    rw [f.property γ x]
    funext F
    change ρ₁ γ.val _ = ρ₂ γ.val _
    rw [h γ.val γ.property]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Two-cocycles for two coefficient systems that agree on the level are the same functions. -/
def castCocycles :
    cocycles rationalLevel (functionRepresentation ρ₁ X) →ₗ[ℂ]
      cocycles rationalLevel (functionRepresentation ρ₂ X) where
  toFun z := ⟨castCochains ρ₁ ρ₂ h X 2 z.val, z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Congruence

theorem endpoint_plane_dualEdge (e : Edges) :
    dualFlag (endpoint .line e) = endpoint .plane (dualEdge e) := by
  have h := endpoint_line_dualEdge (dualEdge e)
  rw [dualEdge_dualEdge] at h
  rw [h, dualFlag_dualPlaneFlag]

section Generic

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
  (h1 : ∀ g ∈ rationalLevel, ρ g = dualRep ρ g) (h2 : ∀ g ∈ rationalLevel, dualRep ρ g = ρ g)

include h1 h2 in
/-- **Dual transport of inner classes.** If `ρ` and `ρ ∘ φ` agree on the level, the vanishing of
the inner line classes of `ρ` gives the vanishing of the inner plane classes of `ρ`. -/
theorem innerBoundaryRep_plane_zero
    (hline : ∀ b : StratumH2Rep ρ .line, InnerBoundaryRep ρ .line b → b = 0)
    {a : StratumH2Rep ρ .plane} (ha : InnerBoundaryRep ρ .plane a) : a = 0 := by
  obtain ⟨z, rfl, u, hu⟩ := ha
  have hu₁ := edgeExact_transport ρ (dualRep ρ) (fun _ => rfl) dualFlag
    dualFlag_smul (endpoint .plane) (endpoint .line) (fun e => endpoint_plane_dualEdge e) z u hu
  have hInner : InnerBoundaryRep ρ .line
      (classOf rationalLevel (flagRepresentation ρ .line)
        (castCocycles (dualRep ρ) ρ h1 (Flags .line) (toLineStar ρ z))) :=
    ⟨castCocycles (dualRep ρ) ρ h1 (Flags .line) (toLineStar ρ z), rfl,
      castCochains (dualRep ρ) ρ h1 Edges 1 (toEdgeStar ρ u), hu₁⟩
  have hz := hline _ hInner
  obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero _).mp hz
  have hs' : boundaryMap rationalLevel (functionRepresentation (dualRep ρ) (Flags .line))
      (castCochains ρ (dualRep ρ) h2 (Flags .line) 1 s) = toLineStar ρ z :=
    Subtype.ext (Subtype.ext (congrArg (fun w => w.val.val) hs))
  refine (Submodule.Quotient.mk_eq_zero _).mpr ⟨transportCochains (dualRep ρ) ρ
    (dualRep_dualRep_apply ρ) dualPlaneFlag dualPlaneFlag_smul 1
    (castCochains ρ (dualRep ρ) h2 (Flags .line) 1 s), ?_⟩
  refine (transportCocycles_boundaryMap (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualPlaneFlag
    dualPlaneFlag_smul (castCochains ρ (dualRep ρ) h2 (Flags .line) 1 s)).symm.trans ?_
  rw [hs']
  exact fromLineStar_toLineStar ρ z

end Generic

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
