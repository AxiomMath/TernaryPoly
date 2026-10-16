module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Model
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Dual.Flags

@[expose] public section


/-!
# The transport maps between `E` and `E* = E ∘ φ` on strata and edges

Specializations of `transportCocycles`/`transportCochains` to `ρ = rationalCoefficientComponent n χ`
and its dual `dualRep ρ`:

* `toLineStar`/`toPlaneStar`: plane (resp. line) cocycles of `E` to line (resp. plane) cocycles
  of `E*` (flag map `dualFlag` resp. `dualPlaneFlag`);
* `fromLineStar`/`fromPlaneStar`: the inverses (`fromLineStar_toLineStar` etc., from
  `dualFlag_dualPlaneFlag`, `dualInvolution_involutive`);
* `toEdgeStar`/`fromEdgeStar` on complete flags (`dualEdge`);
* compatibility with the restriction of global cocycles (`toLineStar_restriction`), with coboundaries
  (`classOf_transport`) and with edge-exactness (`edgeExact_toLineStar`, …).

Formalized by Claude Sonnet 5.5.
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

theorem dualRep_dualRep_apply (g : RationalGL3) : ρ g = dualRep ρ (dualInvolution g) := by
  change ρ g = ρ (dualInvolution (dualInvolution g))
  rw [dualInvolution_involutive]

/-- Plane cocycles of `E` to line cocycles of `E*`. -/
def toLineStar : cocycles rationalLevel (flagRepresentation ρ .plane) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (dualRep ρ) .line) :=
  transportCocycles ρ (dualRep ρ) (fun _ => rfl) dualFlag dualFlag_smul

/-- Line cocycles of `E` to plane cocycles of `E*`. -/
def toPlaneStar : cocycles rationalLevel (flagRepresentation ρ .line) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (dualRep ρ) .plane) :=
  transportCocycles ρ (dualRep ρ) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul

/-- Line cocycles of `E*` to plane cocycles of `E`. -/
def fromLineStar : cocycles rationalLevel (flagRepresentation (dualRep ρ) .line) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation ρ .plane) :=
  transportCocycles (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualPlaneFlag dualPlaneFlag_smul

/-- Plane cocycles of `E*` to line cocycles of `E`. -/
def fromPlaneStar : cocycles rationalLevel (flagRepresentation (dualRep ρ) .plane) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation ρ .line) :=
  transportCocycles (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualFlag dualFlag_smul

/-- One-cochains on complete flags: `E` to `E*`. -/
def toEdgeStar : cochains rationalLevel (functionRepresentation ρ Edges) 1 →ₗ[ℂ]
    cochains rationalLevel (functionRepresentation (dualRep ρ) Edges) 1 :=
  transportCochains ρ (dualRep ρ) (fun _ => rfl) dualEdge dualEdge_smul 1

/-- One-cochains on complete flags: `E*` to `E`. -/
def fromEdgeStar : cochains rationalLevel (functionRepresentation (dualRep ρ) Edges) 1 →ₗ[ℂ]
    cochains rationalLevel (functionRepresentation ρ Edges) 1 :=
  transportCochains (dualRep ρ) ρ (dualRep_dualRep_apply ρ) dualEdge dualEdge_smul 1

theorem toLineStar_restriction (c : cocycles rationalLevel ρ) :
    toLineStar ρ (restrictionCocycleRep ρ .plane c) =
      restrictionCocycleRep (dualRep ρ) .line (phiCocycle ρ c) := rfl

theorem toPlaneStar_restriction (c : cocycles rationalLevel ρ) :
    toPlaneStar ρ (restrictionCocycleRep ρ .line c) =
      restrictionCocycleRep (dualRep ρ) .plane (phiCocycle ρ c) := rfl

theorem fromLineStar_toLineStar (z : cocycles rationalLevel (flagRepresentation ρ .plane)) :
    fromLineStar ρ (toLineStar ρ z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  change z.val.val (fun i => dualInvolution (dualInvolution (x i)))
    (dualFlag (dualPlaneFlag F)) = z.val.val x F
  simp only [dualInvolution_involutive, dualFlag_dualPlaneFlag]

theorem toLineStar_fromLineStar (z : cocycles rationalLevel (flagRepresentation (dualRep ρ) .line)) :
    toLineStar ρ (fromLineStar ρ z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  change z.val.val (fun i => dualInvolution (dualInvolution (x i)))
    (dualPlaneFlag (dualFlag F)) = z.val.val x F
  simp only [dualInvolution_involutive, dualPlaneFlag_dualFlag]

theorem fromPlaneStar_toPlaneStar (z : cocycles rationalLevel (flagRepresentation ρ .line)) :
    fromPlaneStar ρ (toPlaneStar ρ z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  change z.val.val (fun i => dualInvolution (dualInvolution (x i)))
    (dualPlaneFlag (dualFlag F)) = z.val.val x F
  simp only [dualInvolution_involutive, dualPlaneFlag_dualFlag]

theorem toPlaneStar_fromPlaneStar (z : cocycles rationalLevel (flagRepresentation (dualRep ρ) .plane)) :
    toPlaneStar ρ (fromPlaneStar ρ z) = z := by
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  change z.val.val (fun i => dualInvolution (dualInvolution (x i)))
    (dualFlag (dualPlaneFlag F)) = z.val.val x F
  simp only [dualInvolution_involutive, dualFlag_dualPlaneFlag]

/-- Transport carries cohomologous cocycles to cohomologous cocycles. -/
theorem classOf_transport {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X']
    (ρ₁ ρ₂ : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ₂ g = ρ₁ (dualInvolution g))
    (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = dualInvolution g • m F)
    {z₁ z₂ : cocycles rationalLevel (functionRepresentation ρ₁ X)}
    (h : classOf rationalLevel (functionRepresentation ρ₁ X) z₁ =
      classOf rationalLevel (functionRepresentation ρ₁ X) z₂) :
    classOf rationalLevel (functionRepresentation ρ₂ X') (transportCocycles ρ₁ ρ₂ hρ m hm z₁) =
      classOf rationalLevel (functionRepresentation ρ₂ X') (transportCocycles ρ₁ ρ₂ hρ m hm z₂) := by
  obtain ⟨s, hs⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.eq _).mp h)
  apply (Submodule.Quotient.eq _).mpr
  refine LinearMap.mem_range.mpr ⟨transportCochains ρ₁ ρ₂ hρ m hm 1 s, ?_⟩
  rw [← transportCocycles_boundaryMap, hs, map_sub]

/-- Edge exactness of a flag cocycle transports along the dual flag maps. -/
theorem edgeExact_transport {X X' : Type} [MulAction RationalGL3 X] [MulAction RationalGL3 X']
    (ρ₁ ρ₂ : Representation ℂ RationalGL3 V) (hρ : ∀ g, ρ₂ g = ρ₁ (dualInvolution g))
    (m : X' → X) (hm : ∀ (g : RationalGL3) F, m (g • F) = dualInvolution g • m F)
    (π : Edges → X) (π' : Edges → X') (hπ : ∀ e, m (π' e) = π (dualEdge e))
    (z : cocycles rationalLevel (functionRepresentation ρ₁ X))
    (u : cochains rationalLevel (functionRepresentation ρ₁ Edges) 1)
    (hu : ∀ x e, z.val.val x (π e) =
      (differentialOne rationalLevel (functionRepresentation ρ₁ Edges) u).val x e) :
    ∀ x e, (transportCocycles ρ₁ ρ₂ hρ m hm z).val.val x (π' e) =
      (differentialOne rationalLevel (functionRepresentation ρ₂ Edges)
        (transportCochains ρ₁ ρ₂ hρ dualEdge dualEdge_smul 1 u)).val x e := by
  intro x e
  rw [← transportCochains_differentialOne]
  change z.val.val (fun i => dualInvolution (x i)) (m (π' e)) =
    (differentialOne rationalLevel (functionRepresentation ρ₁ Edges) u).val
      (fun i => dualInvolution (x i)) (dualEdge e)
  rw [hπ, hu]

end TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
