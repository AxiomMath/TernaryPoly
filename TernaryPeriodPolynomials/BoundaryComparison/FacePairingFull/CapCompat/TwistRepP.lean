module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.CapCompat.TwistRep
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.CupP

@[expose] public section

/-!
# Twisting model cochains by the plane duality data: function-level plumbing (the plane twin of `TwistRep`)

Mirror of `TwistRep` under the exchange of the line and plane sides.  For `T : DualityDataP n χ` (with
`ρ = rationalCoefficientComponent n χ`) the line cochain `y` and the edge cochain `s` of the arithmetic level are transported
to plane cochains of `N6` with the twisted coefficients `twistRepP T = ρ ∘ φ`:

* `twistCochain2P T y`: `(x, F) ↦ y (φ x) (dualFlag F)` for a line two-cochain `y` (`twistCochain2P_apply`, `twistCochain2P_cocycle`);
* `twistCochain1P T s`: the same for an edge one-cochain via `dualEdge`;
* `twistP_edge_compat`: if `y` restricts on complete flags to the coboundary of `s`, then `twistCochain2P T y` restricts on complete
  flags to the coboundary of `twistCochain1P T s`;
* `pairHomP T r : coeffRep (twistRepP T) ⟶ dualRepresentation (coeffRep ρ)`.

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityDataP n χ)

/-- The `φ`-twist of the coefficient representation. -/
def twistRepP : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  (rationalCoefficientComponent n χ).comp T.φ

theorem twistRepP_apply (g : RationalGL3) (v : HomogeneousPoly n) :
    twistRepP T g v = rationalCoefficientComponent n χ (T.φ g) v := rfl

section Twist

theorem vec3_phiP (a b c : RationalGL3) :
    (fun i => T.φ ((![a, b, c] : Fin 3 → RationalGL3) i)) = ![T.φ a, T.φ b, T.φ c] := by
  funext i; fin_cases i <;> rfl

theorem vec2_phiP (a b : RationalGL3) :
    (fun i => T.φ ((![a, b] : Fin 2 → RationalGL3) i)) = ![T.φ a, T.φ b] := by
  funext i; fin_cases i <;> rfl

/-- The `φ`-transport of a line degree-two cochain to a plane cochain with the twisted coefficients. -/
def twistCochain2P (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) 2) :
    cochains N6 (functionRepresentation (twistRepP T) (Flags .plane)) 2 :=
  ⟨fun x F => y.1 (fun i => T.φ (x i)) (T.dualFlag F), by
    intro g x
    funext F
    have hg : T.φ g.val ∈ rationalLevel := T.level g.val (N6_le_rationalLevel g.property)
    have h1 := congrFun (y.2 ⟨T.φ g.val, hg⟩ (fun i => T.φ (x i))) (T.dualFlag F)
    change y.1 (fun i => T.φ (g.val * x i)) (T.dualFlag F) =
      twistRepP T g.val (y.1 (fun i => T.φ (x i)) (T.dualFlag (g.val⁻¹ • F)))
    simp only [map_mul]
    refine h1.trans ?_
    change rationalCoefficientComponent n χ (T.φ g.val)
        (y.1 (fun i => T.φ (x i)) ((T.φ g.val)⁻¹ • T.dualFlag F)) = _
    rw [← map_inv T.φ g.val, ← T.dualFlag_smul]
    rfl⟩

theorem twistCochain2P_apply (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) 2)
    (x : Fin 3 → RationalGL3) (F : Flags .plane) :
    (twistCochain2P T y).1 x F = y.1 (fun i => T.φ (x i)) (T.dualFlag F) := rfl

/-- The `φ`-transport of an edge degree-one cochain. -/
def twistCochain1P (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1) :
    cochains N6 (functionRepresentation (twistRepP T) Edges) 1 :=
  ⟨fun x e => s.1 (fun i => T.φ (x i)) (T.dualEdge e), by
    intro g x
    funext e
    have hg : T.φ g.val ∈ rationalLevel := T.level g.val (N6_le_rationalLevel g.property)
    have h1 := congrFun (s.2 ⟨T.φ g.val, hg⟩ (fun i => T.φ (x i))) (T.dualEdge e)
    change s.1 (fun i => T.φ (g.val * x i)) (T.dualEdge e) =
      twistRepP T g.val (s.1 (fun i => T.φ (x i)) (T.dualEdge (g.val⁻¹ • e)))
    simp only [map_mul]
    refine h1.trans ?_
    change rationalCoefficientComponent n χ (T.φ g.val)
        (s.1 (fun i => T.φ (x i)) ((T.φ g.val)⁻¹ • T.dualEdge e)) = _
    rw [← map_inv T.φ g.val, ← T.dualEdge_smul]
    rfl⟩

theorem twistCochain1P_apply (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1)
    (x : Fin 2 → RationalGL3) (e : Edges) :
    (twistCochain1P T s).1 x e = s.1 (fun i => T.φ (x i)) (T.dualEdge e) := rfl

theorem twistCochain2P_cocycle
    (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) 2)
    (hy : differentialTwo rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) y = 0) :
    differentialTwo N6 (functionRepresentation (twistRepP T) (Flags .plane)) (twistCochain2P T y) = 0 := by
  funext x F
  have h := congrFun (congrFun hy (fun i => T.φ (x i))) (T.dualFlag F)
  change y.1 (fun i => T.φ ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) -
      y.1 (fun i => T.φ ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) +
      y.1 (fun i => T.φ ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) -
      y.1 (fun i => T.φ ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) (T.dualFlag F) = 0
  simp only [vec3_phiP]
  exact h

theorem twistP_edge_compat
    (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .line) 2)
    (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1)
    (hs : ∀ x e, y.1 x (endpoint .line e) = differentialOneRaw s.1 x e) :
    ∀ x e, (twistCochain2P T y).1 x (endpoint .plane e) =
      (differentialOne N6 (functionRepresentation (twistRepP T) Edges) (twistCochain1P T s)).1 x e := by
  intro x e
  change y.1 (fun i => T.φ (x i)) (T.dualFlag (endpoint .plane e)) =
    s.1 (fun i => T.φ ((![x 1, x 2] : Fin 2 → RationalGL3) i)) (T.dualEdge e) -
      s.1 (fun i => T.φ ((![x 0, x 2] : Fin 2 → RationalGL3) i)) (T.dualEdge e) +
      s.1 (fun i => T.φ ((![x 0, x 1] : Fin 2 → RationalGL3) i)) (T.dualEdge e)
  simp only [vec2_phiP]
  rw [← T.endpoint_dualEdge, hs]
  rfl

end Twist

section Pairing

open TernaryPoly.SingularLocalDuality

/-- The `ℚ`-bilinear pairing `(w, v) ↦ r (B(v, w))`. -/
def pairLinP (r : ℂ →ₗ[ℚ] ℚ) : HomogeneousPoly n →ₗ[ℚ] Module.Dual ℚ (HomogeneousPoly n) :=
  LinearMap.mk₂ ℚ (fun w v => r (T.B v w))
    (fun a b v => by simp)
    (fun c w v => by simp)
    (fun w a b => by simp)
    (fun c w v => by simp)

theorem pairLinP_apply (r : ℂ →ₗ[ℚ] ℚ) (w v : HomogeneousPoly n) : pairLinP T r w v = r (T.B v w) := rfl

theorem pairLinP_equivariant (r : ℂ →ₗ[ℚ] ℚ) (γ : Γ6) (w v : HomogeneousPoly n) :
    pairLinP T r (rationalCoefficientComponent n χ (T.φ (iotaQ γ)) w) v =
      pairLinP T r w (rationalCoefficientComponent n χ (iotaQ γ⁻¹) v) := by
  rw [map_inv]
  have hg : iotaQ γ ∈ rationalLevel := N6_le_rationalLevel (iotaQ_mem γ)
  have h := T.invariant (iotaQ γ) hg (rationalCoefficientComponent n χ (iotaQ γ)⁻¹ v) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact congrArg r h

/-- The pairing homomorphism from the twisted representation to the contragredient of the untwisted one. -/
def pairHomP (r : ℂ →ₗ[ℚ] ℚ) :
    coeffRep (twistRepP T) ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n χ)) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (pairLinP T r : (coeffRep (twistRepP T)) →ₗ[ℚ] Module.Dual ℚ (coeffRep (rationalCoefficientComponent n χ)))
    (fun γ w => by
      apply LinearMap.ext
      intro v
      change pairLinP T r (rationalCoefficientComponent n χ (T.φ (iotaQ γ)) w) v =
        dualValue ((dualRepresentation (coeffRep (rationalCoefficientComponent n χ))).ρ γ
          (pairLinP T r w)) v
      exact (pairLinP_equivariant T r γ w v).trans
        (dualRepresentation_apply (coeffRep (rationalCoefficientComponent n χ)) γ (pairLinP T r w) v).symm))

theorem pairHomP_apply (r : ℂ →ₗ[ℚ] ℚ) (w : HomogeneousPoly n) (v : HomogeneousPoly n) :
    dualValue ((pairHomP T r).hom w) v = r (T.B v w) := rfl

end Pairing

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
