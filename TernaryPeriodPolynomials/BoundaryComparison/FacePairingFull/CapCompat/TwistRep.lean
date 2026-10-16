module

public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.InnerLift
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Model.Cup
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Comparison.Coefficients

@[expose] public section

/-!
# Twisting model cochains by the duality data: function-level plumbing

For `T : DualityData n χ` (with `ρ = rationalCoefficientComponent n χ`) this file turns the function-level objects of
the model boundary cup product into `Γ(6)`-equivariant homogeneous cochains with the twisted coefficients
`twistRep T = ρ ∘ φ`, ready for `modelHomOf`.

* `twistRep`: the representation `ρ ∘ T.φ` (so `coeffRep (twistRep T)` is a representation of `Γ(6)`);
* `restrictN6`: restriction of homogeneous cochains from `rationalLevel` to `N6`
  (`restrictN6_cocycle`, `restrictN6_differentialOne`, `differentialOne_apply_raw`);
* `twistCochain2 T y`: `(x, F) ↦ y (φ x) (dualFlag F)` for a plane two-cochain `y` of the arithmetic level, a line
  cochain of `N6` with coefficients `twistRep T` (`twistCochain2_apply`, `twistCochain2_cocycle`);
* `twistCochain1 T s`: the same for an edge one-cochain via `dualEdge` (`twistCochain1_apply`);
* `twist_edge_compat`: if `y` restricts on complete flags to the coboundary of `s`, then `twistCochain2 T y`
  restricts on complete flags to the coboundary of `twistCochain1 T s`;
* `pairHom T r : coeffRep (twistRep T) ⟶ dualRepresentation (coeffRep ρ)`, `w ↦ (v ↦ r (B(v, w)))`, for a
  `ℚ`-linear `r : ℂ → ℚ` (`pairHom_apply`).

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Limits
open GeneralEisenstein GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison

variable {n : ℕ} {χ : RankOneCharacter} (T : DualityData n χ)

/-- The `φ`-twist of the coefficient representation. -/
def twistRep : Representation ℂ RationalGL3 (HomogeneousPoly n) :=
  (rationalCoefficientComponent n χ).comp T.φ

theorem twistRep_apply (g : RationalGL3) (v : HomogeneousPoly n) :
    twistRep T g v = rationalCoefficientComponent n χ (T.φ g) v := rfl

section Restrict

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ' : Representation ℂ RationalGL3 V)

/-- Restriction of homogeneous cochains from the arithmetic level to `Γ(6)`-equivariant ones. -/
def restrictN6 {k : ℕ} : cochains rationalLevel ρ' k →ₗ[ℂ] cochains N6 ρ' k :=
  Submodule.inclusion (cochains_mono ρ' N6_le_rationalLevel k)

theorem restrictN6_apply {k : ℕ} (f : cochains rationalLevel ρ' k) (x : Fin (k + 1) → RationalGL3) :
    (restrictN6 ρ' f).1 x = f.1 x := rfl

theorem restrictN6_cocycle (f : cochains rationalLevel ρ' 2)
    (hf : differentialTwo rationalLevel ρ' f = 0) :
    differentialTwo N6 ρ' (restrictN6 ρ' f) = 0 := hf

theorem restrictN6_differentialOne (f : cochains rationalLevel ρ' 1) :
    differentialOne N6 ρ' (restrictN6 ρ' f) = restrictN6 ρ' (differentialOne rationalLevel ρ' f) := rfl

theorem differentialOne_apply_raw (Γ : Subgroup RationalGL3) (f : cochains Γ ρ' 1) (x : Fin 3 → RationalGL3) :
    (differentialOne Γ ρ' f).1 x = differentialOneRaw f.1 x := rfl

end Restrict

section Twist

theorem vec3_phi (a b c : RationalGL3) :
    (fun i => T.φ ((![a, b, c] : Fin 3 → RationalGL3) i)) = ![T.φ a, T.φ b, T.φ c] := by
  funext i; fin_cases i <;> rfl

theorem vec2_phi (a b : RationalGL3) :
    (fun i => T.φ ((![a, b] : Fin 2 → RationalGL3) i)) = ![T.φ a, T.φ b] := by
  funext i; fin_cases i <;> rfl

/-- The `φ`-transport of a plane degree-two cochain to a line cochain with the twisted coefficients. -/
def twistCochain2 (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) 2) :
    cochains N6 (functionRepresentation (twistRep T) (Flags .line)) 2 :=
  ⟨fun x F => y.1 (fun i => T.φ (x i)) (T.dualFlag F), by
    intro g x
    funext F
    have hg : T.φ g.val ∈ rationalLevel := T.level g.val (N6_le_rationalLevel g.property)
    have h1 := congrFun (y.2 ⟨T.φ g.val, hg⟩ (fun i => T.φ (x i))) (T.dualFlag F)
    change y.1 (fun i => T.φ (g.val * x i)) (T.dualFlag F) =
      twistRep T g.val (y.1 (fun i => T.φ (x i)) (T.dualFlag (g.val⁻¹ • F)))
    simp only [map_mul]
    refine h1.trans ?_
    change rationalCoefficientComponent n χ (T.φ g.val)
        (y.1 (fun i => T.φ (x i)) ((T.φ g.val)⁻¹ • T.dualFlag F)) = _
    rw [← map_inv T.φ g.val, ← T.dualFlag_smul]
    rfl⟩

theorem twistCochain2_apply (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) 2)
    (x : Fin 3 → RationalGL3) (F : Flags .line) :
    (twistCochain2 T y).1 x F = y.1 (fun i => T.φ (x i)) (T.dualFlag F) := rfl

/-- The `φ`-transport of an edge degree-one cochain. -/
def twistCochain1 (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1) :
    cochains N6 (functionRepresentation (twistRep T) Edges) 1 :=
  ⟨fun x e => s.1 (fun i => T.φ (x i)) (T.dualEdge e), by
    intro g x
    funext e
    have hg : T.φ g.val ∈ rationalLevel := T.level g.val (N6_le_rationalLevel g.property)
    have h1 := congrFun (s.2 ⟨T.φ g.val, hg⟩ (fun i => T.φ (x i))) (T.dualEdge e)
    change s.1 (fun i => T.φ (g.val * x i)) (T.dualEdge e) =
      twistRep T g.val (s.1 (fun i => T.φ (x i)) (T.dualEdge (g.val⁻¹ • e)))
    simp only [map_mul]
    refine h1.trans ?_
    change rationalCoefficientComponent n χ (T.φ g.val)
        (s.1 (fun i => T.φ (x i)) ((T.φ g.val)⁻¹ • T.dualEdge e)) = _
    rw [← map_inv T.φ g.val, ← T.dualEdge_smul]
    rfl⟩

theorem twistCochain1_apply (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1)
    (x : Fin 2 → RationalGL3) (e : Edges) :
    (twistCochain1 T s).1 x e = s.1 (fun i => T.φ (x i)) (T.dualEdge e) := rfl

theorem twistCochain2_cocycle
    (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) 2)
    (hy : differentialTwo rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) y = 0) :
    differentialTwo N6 (functionRepresentation (twistRep T) (Flags .line)) (twistCochain2 T y) = 0 := by
  funext x F
  have h := congrFun (congrFun hy (fun i => T.φ (x i))) (T.dualFlag F)
  change y.1 (fun i => T.φ ((![x 1, x 2, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) -
      y.1 (fun i => T.φ ((![x 0, x 2, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) +
      y.1 (fun i => T.φ ((![x 0, x 1, x 3] : Fin 3 → RationalGL3) i)) (T.dualFlag F) -
      y.1 (fun i => T.φ ((![x 0, x 1, x 2] : Fin 3 → RationalGL3) i)) (T.dualFlag F) = 0
  simp only [vec3_phi]
  exact h

theorem twist_edge_compat
    (y : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) .plane) 2)
    (s : cochains rationalLevel (functionRepresentation (rationalCoefficientComponent n χ) Edges) 1)
    (hs : ∀ x e, y.1 x (endpoint .plane e) = differentialOneRaw s.1 x e) :
    ∀ x e, (twistCochain2 T y).1 x (endpoint .line e) =
      (differentialOne N6 (functionRepresentation (twistRep T) Edges) (twistCochain1 T s)).1 x e := by
  intro x e
  change y.1 (fun i => T.φ (x i)) (T.dualFlag (endpoint .line e)) =
    s.1 (fun i => T.φ ((![x 1, x 2] : Fin 2 → RationalGL3) i)) (T.dualEdge e) -
      s.1 (fun i => T.φ ((![x 0, x 2] : Fin 2 → RationalGL3) i)) (T.dualEdge e) +
      s.1 (fun i => T.φ ((![x 0, x 1] : Fin 2 → RationalGL3) i)) (T.dualEdge e)
  simp only [vec2_phi]
  rw [← T.endpoint_dualEdge, hs]
  rfl

end Twist

section Pairing

open TernaryPoly.SingularLocalDuality

/-- The `ℚ`-bilinear pairing `(w, v) ↦ r (B(v, w))`. -/
def pairLin (r : ℂ →ₗ[ℚ] ℚ) : HomogeneousPoly n →ₗ[ℚ] Module.Dual ℚ (HomogeneousPoly n) :=
  LinearMap.mk₂ ℚ (fun w v => r (T.B v w))
    (fun a b v => by simp)
    (fun c w v => by simp)
    (fun w a b => by simp)
    (fun c w v => by simp)

theorem pairLin_apply (r : ℂ →ₗ[ℚ] ℚ) (w v : HomogeneousPoly n) : pairLin T r w v = r (T.B v w) := rfl

theorem pairLin_equivariant (r : ℂ →ₗ[ℚ] ℚ) (γ : Γ6) (w v : HomogeneousPoly n) :
    pairLin T r (rationalCoefficientComponent n χ (T.φ (iotaQ γ)) w) v =
      pairLin T r w (rationalCoefficientComponent n χ (iotaQ γ⁻¹) v) := by
  rw [map_inv]
  have hg : iotaQ γ ∈ rationalLevel := N6_le_rationalLevel (iotaQ_mem γ)
  have h := T.invariant (iotaQ γ) hg (rationalCoefficientComponent n χ (iotaQ γ)⁻¹ v) w
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at h
  exact congrArg r h

/-- The pairing homomorphism from the twisted representation to the contragredient of the untwisted one. -/
def pairHom (r : ℂ →ₗ[ℚ] ℚ) :
    coeffRep (twistRep T) ⟶ dualRepresentation (coeffRep (rationalCoefficientComponent n χ)) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (pairLin T r : (coeffRep (twistRep T)) →ₗ[ℚ] Module.Dual ℚ (coeffRep (rationalCoefficientComponent n χ)))
    (fun γ w => by
      apply LinearMap.ext
      intro v
      change pairLin T r (rationalCoefficientComponent n χ (T.φ (iotaQ γ)) w) v =
        dualValue ((dualRepresentation (coeffRep (rationalCoefficientComponent n χ))).ρ γ
          (pairLin T r w)) v
      exact (pairLin_equivariant T r γ w v).trans
        (dualRepresentation_apply (coeffRep (rationalCoefficientComponent n χ)) γ (pairLin T r w) v).symm))

theorem pairHom_apply (r : ℂ →ₗ[ℚ] ℚ) (w : HomogeneousPoly n) (v : HomogeneousPoly n) :
    dualValue ((pairHom T r).hom w) v = r (T.B v w) := rfl

end Pairing

end TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
