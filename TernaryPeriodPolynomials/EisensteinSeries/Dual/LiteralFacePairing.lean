module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralDualModel
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.TraceDetects
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.FacePairingForm

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.ChainLocal (lineValue)
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual

/-!
# The face pairing for the literal dual `E*`: literal trace, inner classes, `facePairingLit`

Formalized by Claude Sonnet 5.5.

The model face pairing `FacePairingFull.facePairing`
pairs inner line classes of `E` with inner PLANE classes of `E`, the latter standing for the line classes of `E*` through the involution `φ`
(`traceValue z w y = Σ_v lineValue …`, with the model pairing `dualPairing(·, y^φ(dualFlag ·))`).  Here:

* `litLineValue`, `traceValueLit`: the same trace formula with `dualPairing(·, y^φ(dualFlag ·))` replaced by evaluation of an `E*`-valued line
  cocycle `y''` (`E*` the contragredient `(rationalCoefficientComponent n triv).dual`);
* `traceValueLit_eq`: it equals the model `traceValue` at the plane cocycle `fromLineStar (Θ⁻¹ y'')`, with scalar `1` (`fromLine_val`, `pairing_literal`);
* `planeLitEquiv : H²(plane; E) ≃ₗ H²(line; E*)` (`Θ ∘ toLineStar` on cocycles, `fromLineStar ∘ Θ⁻¹` back; compatible with coboundaries) and its
  restriction `innerPlaneLitEquiv` to inner (zero flag restriction) classes (`planeLit_inner`, `litPlane_inner`);
* `facePairingLit : 𝒞_Q(E) × 𝒞_Q(E*) → ℂ`, and `facePairingLit_eq_traceValueLit`: it is the literal trace for any representatives and edge primitive.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (n : ℕ)

/-- Value of the model plane cocycle `fromLineStar (Θ⁻¹ y'')` at the dual tuples and dual flag. -/
theorem fromLine_val
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line))
    (a b c : RationalGL3) (F : Flags .line) :
    (fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) y'')).val.val
        ![dualInvolution a, dualInvolution b, dualInvolution c] (dualFlag F) =
      (thetaModelEquiv n).symm (y''.val.val ![a, b, c] F) := by
  change (thetaXInvCocycles n (Flags .line) y'').val.val
      (fun i => dualInvolution ((![dualInvolution a, dualInvolution b, dualInvolution c] : Fin 3 → RationalGL3) i))
      (dualPlaneFlag (dualFlag F)) = _
  rw [phi_vec3_inv, dualPlaneFlag_dualFlag]
  rfl

/-- **The local value of the face-pairing trace for the literal dual `E*`**: the formula of `ChainLocal.lineValue` with the model pairing
`dualPairing(·, y^φ(dualFlag ·))` replaced by evaluation of the `E*`-valued line cocycle `y''`. -/
def litLineValue {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
    (Θ : TraceData ι L P) (v : L)
    (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)) : ℂ :=
  (∑ i ∈ Finset.univ.filter (fun i => Θ.lineOf i = v),
      Finsupp.linearCombination ℂ (fun x => (y''.val.val ![x 1, x 2, x 3] (Θ.lineRep v))
        (w.val ![x 0, x 1] (Θ.edge i))) (Θ.chain i)) -
    Finsupp.linearCombination ℂ (fun x => (y''.val.val ![x 2, x 3, x 4] (Θ.lineRep v))
      (z.val.val ![x 0, x 1, x 2] (Θ.lineRep v))) (Θ.lineFill v)

/-- **The trace pairing for the literal dual**: sum of the local values at the two line cusps. -/
def traceValueLit (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)) : ℂ :=
  ∑ v : Fin 2, litLineValue n traceDataL2 v z w y''

/-- The literal trace is the model trace of the corresponding plane cocycle (same value, scalar `1`). -/
theorem traceValueLit_eq (z : MaximalCycles n trivialCharacter .line) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)) :
    traceValueLit n z w y'' =
      traceValue z w (fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) y'')) := by
  unfold traceValueLit traceValue
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold litLineValue lineValue
  have e1 : ∀ i, (fun x : Fin 4 → RationalGL3 => (y''.val.val ![x 1, x 2, x 3] (traceDataL2.lineRep v))
        (w.val ![x 0, x 1] (traceDataL2.edge i))) =
      fun x => (dualityData n trivialCharacter).B (w.val ![x 0, x 1] (traceDataL2.edge i))
        ((fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) y'')).val.val
          ![(dualityData n trivialCharacter).φ (x 1), (dualityData n trivialCharacter).φ (x 2),
            (dualityData n trivialCharacter).φ (x 3)]
          ((dualityData n trivialCharacter).dualFlag (traceDataL2.lineRep v))) := by
    intro i
    funext x
    change _ = dualPairing n _ _
    erw [fromLine_val, pairing_literal]
  have e2 : (fun x : Fin 5 → RationalGL3 => (y''.val.val ![x 2, x 3, x 4] (traceDataL2.lineRep v))
        (z.val.val ![x 0, x 1, x 2] (traceDataL2.lineRep v))) =
      fun x => (dualityData n trivialCharacter).B (z.val.val ![x 0, x 1, x 2] (traceDataL2.lineRep v))
        ((fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) y'')).val.val
          ![(dualityData n trivialCharacter).φ (x 2), (dualityData n trivialCharacter).φ (x 3),
            (dualityData n trivialCharacter).φ (x 4)]
          ((dualityData n trivialCharacter).dualFlag (traceDataL2.lineRep v))) := by
    funext x
    change _ = dualPairing n _ _
    erw [fromLine_val, pairing_literal]
  simp only [e1, e2]

section Strata

variable (n : ℕ)

/-- `E`-plane cocycles to `E*`-line cocycles: `Θ ∘ toLineStar`. -/
def planeToLitCocycles : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) :=
  (thetaXCocycles n (Flags .line)) ∘ₗ (toLineStar (rationalCoefficientComponent n trivialCharacter))

/-- `E*`-line cocycles to `E`-plane cocycles: `fromLineStar ∘ Θ⁻¹`. -/
def litToPlaneCocycles : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) :=
  (fromLineStar (rationalCoefficientComponent n trivialCharacter)) ∘ₗ (thetaXInvCocycles n (Flags .line))

theorem litToPlane_planeToLit (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)) :
    litToPlaneCocycles n (planeToLitCocycles n z) = z := by
  have e : thetaXInvCocycles n (Flags .line) (thetaXCocycles n (Flags .line) (toLineStar (rationalCoefficientComponent n trivialCharacter) z)) = toLineStar (rationalCoefficientComponent n trivialCharacter) z := by
    apply Subtype.ext
    apply Subtype.ext
    funext x F
    exact congrFun (thetaFunInv_thetaFun n (Flags .line) ((toLineStar (rationalCoefficientComponent n trivialCharacter) z).val.val x)) F
  change fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) (thetaXCocycles n (Flags .line) (toLineStar (rationalCoefficientComponent n trivialCharacter) z))) = z
  rw [e, fromLineStar_toLineStar]

theorem planeToLit_litToPlane (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)) :
    planeToLitCocycles n (litToPlaneCocycles n z) = z := by
  change thetaXCocycles n (Flags .line) (toLineStar (rationalCoefficientComponent n trivialCharacter) (fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) z))) = z
  have e := toLineStar_fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) z)
  rw [e]
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  exact congrFun (thetaFun_thetaFunInv n (Flags .line) (z.val.val x)) F

theorem planeToLit_boundary
    (s : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) 1) :
    planeToLitCocycles n (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) s) =
      boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)
        (thetaXCochains n (Flags .line)
          1 (transportCochains (rationalCoefficientComponent n trivialCharacter)
            (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualFlag dualFlag_smul 1 s)) := by
  have h := transportCocycles_boundaryMap (rationalCoefficientComponent n trivialCharacter)
    (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualFlag dualFlag_smul s
  exact (congrArg (thetaXCocycles n (Flags .line)) h).trans
    (coeffCocycles_boundaryMap rationalLevel _ _ _ _ _)

/-- The induced map on cohomology of the strata: plane classes of `E` ↦ line classes of `E*`. -/
def planeToLitH2 : StratumH2 n trivialCharacter .plane →ₗ[ℂ] StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line :=
  Submodule.mapQ _ _ (planeToLitCocycles n) (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (planeToLit_boundary n s).symm⟩)

theorem litToPlane_boundary
    (s : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) 1) :
    litToPlaneCocycles n (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) s) =
      boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        (transportCochains (dualRep (rationalCoefficientComponent n trivialCharacter))
          (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualPlaneFlag dualPlaneFlag_smul 1
          (thetaXInvCochains n (Flags .line) 1 s)) := by
  have h1 : thetaXInvCocycles n (Flags .line)
      (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) s) =
      boundaryMap rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) (Flags .line))
        (thetaXInvCochains n (Flags .line) 1 s) :=
    coeffCocycles_boundaryMap rationalLevel _ _ _ _ _
  have h := transportCocycles_boundaryMap (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualPlaneFlag dualPlaneFlag_smul
    (thetaXInvCochains n (Flags .line) 1 s)
  exact (congrArg (fromLineStar (rationalCoefficientComponent n trivialCharacter)) h1).trans h

def litToPlaneH2 : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line →ₗ[ℂ] StratumH2 n trivialCharacter .plane :=
  Submodule.mapQ _ _ (litToPlaneCocycles n) (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (litToPlane_boundary n s).symm⟩)

/-- **The strata isomorphism** `H²(Γ, flags_P; E) ≃ H²(Γ, flags_L; E*)`, `Θ ∘ (c ↦ c∘φ)`. -/
def planeLitEquiv : StratumH2 n trivialCharacter .plane ≃ₗ[ℂ] StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line :=
  LinearEquiv.ofLinearMap (planeToLitH2 n) (litToPlaneH2 n)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      change (planeToLitH2 n) ((litToPlaneH2 n) (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
      simp only [litToPlaneH2, planeToLitH2, Submodule.mapQ_apply]
      rw [planeToLit_litToPlane])
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      change (litToPlaneH2 n) ((planeToLitH2 n) (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
      simp only [litToPlaneH2, planeToLitH2, Submodule.mapQ_apply]
      rw [litToPlane_planeToLit])

theorem planeLitEquiv_mk (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)) :
    planeLitEquiv n (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z) =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)
        (planeToLitCocycles n z) := rfl

theorem planeLitEquiv_symm_mk (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line)) :
    (planeLitEquiv n).symm (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) z) =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
        (litToPlaneCocycles n z) := rfl

theorem planeLit_inner (ξ : StratumH2 n trivialCharacter .plane) (hξ : InnerBoundary n trivialCharacter .plane ξ) :
    InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .line (planeLitEquiv n ξ) := by
  obtain ⟨y0, hy0, u, hu⟩ := hξ
  subst hy0
  rw [planeLitEquiv_mk]
  have h1 := edgeExact_transport (rationalCoefficientComponent n trivialCharacter)
    (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualFlag dualFlag_smul
    (endpoint .plane) (endpoint .line) (fun e => (endpoint_plane_dualEdge e).symm) y0 u hu
  refine inner_theta n .line (toLineStar (rationalCoefficientComponent n trivialCharacter) y0)
    (toEdgeStar (rationalCoefficientComponent n trivialCharacter) u) (fun x e => h1 x e)

theorem litPlane_inner
    (η : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .line)
    (hη : InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .line η) :
    InnerBoundary n trivialCharacter .plane ((planeLitEquiv n).symm η) := by
  obtain ⟨z', hz', u', hu'⟩ := hη
  subst hz'
  rw [planeLitEquiv_symm_mk]
  obtain ⟨z0, hz0, u0, hu0⟩ := inner_theta_inv n .line z' u' hu'
  have h1 := edgeExact_transport (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualPlaneFlag dualPlaneFlag_smul
    (endpoint .line) (endpoint .plane) (fun e => (endpoint_line_dualEdge e).symm) z0 u0 hu0
  refine ⟨fromLineStar (rationalCoefficientComponent n trivialCharacter) z0, ?_,
    transportCochains (dualRep (rationalCoefficientComponent n trivialCharacter))
      (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualEdge dualEdge_smul 1 u0,
    fun x e => h1 x e⟩
  exact classOf_transport (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualPlaneFlag dualPlaneFlag_smul hz0

/-- The inner (mixed cuspidal) plane classes of `E` correspond to the inner line classes of `E*`. -/
def innerPlaneLitEquiv : innerClasses n .plane ≃ₗ[ℂ]
    innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line :=
  LinearEquiv.ofSubmodules (planeLitEquiv n) (innerClasses n .plane)
    (innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line) (by
      ext η
      rw [Submodule.mem_map_equiv]
      constructor
      · intro h
        have h' := planeLit_inner n ((planeLitEquiv n).symm η) h
        rwa [LinearEquiv.apply_symm_apply] at h'
      · intro h
        exact litPlane_inner n η h)

/-- **The face pairing `⟨ , ⟩_Q` for the literal dual `E*`**: `𝒞_Q(E) × 𝒞_Q(E*) → ℂ`, the model pairing carried through `Θ`.
`facePairingLit_eq_traceValueLit` shows it is intrinsic: the trace of the boundary cup product computed with the evaluation pairing. -/
def facePairingLit : innerClasses n .line →ₗ[ℂ]
    innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line →ₗ[ℂ] ℂ :=
  LinearMap.compl₂ (facePairing n)
    ((innerPlaneLitEquiv n).symm : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line →ₗ[ℂ] innerClasses n .plane)

/-- **Representative independence for the literal dual**: for any representatives `z` of `b`, edge primitive `w`, and `E*`-line cocycle `y''`
representing `η`, the literal face pairing is the literal trace `traceValueLit z w y''`. -/
theorem facePairingLit_eq_traceValueLit (b : innerClasses n .line)
    (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .line)
    (z : MaximalCycles n trivialCharacter .line)
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z = b.1)
    (w : EdgeCochains n trivialCharacter 1) (hw : EdgePrimitive z w)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line))
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .line) y'' = η.1) :
    facePairingLit n b η = traceValueLit n z w y'' := by
  have hξ : InnerBoundary n trivialCharacter .plane ((planeLitEquiv n).symm η.1) := litPlane_inner n η.1 η.2
  have hclass : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane)
      (litToPlaneCocycles n y'') = (planeLitEquiv n).symm η.1 := by
    rw [← hy]
    exact (planeLitEquiv_symm_mk n y'').symm
  have h := pairingValue_eq b.2 hξ hz hw hclass
  have e0 : facePairingLit n b η = pairingValue n b.1 ((planeLitEquiv n).symm η.1) := rfl
  have e : litToPlaneCocycles n y'' =
      fromLineStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .line) y'') := rfl
  rw [e0, h, traceValueLit_eq, e]

end Strata

end TernaryPeriodPolynomials.Argument.EisensteinDual
