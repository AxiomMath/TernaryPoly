module

public import TernaryPeriodPolynomials.EisensteinSeries.Dual.LiteralFacePairing
public import TernaryPeriodPolynomials.BoundaryComparison.FacePairingFull.Plane.Pairing

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Homogeneous TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains
open TernaryPeriodPolynomials.BoundaryDuality.L2Trace (traceDataL2)
open TernaryPeriodPolynomials.Argument.FacePairingFull
open TernaryPeriodPolynomials.Argument.FacePairingFull.Dual
open TernaryPeriodPolynomials.Argument.FacePairingFull.Plane

/-!
# The plane face pairing for the literal dual `E*`

Formalized by Claude Sonnet 5.5.

Mirror (exchange of the line and plane sides) of `EisensteinDual.LiteralFacePairing`:
the model plane face pairing `Plane.facePairingP : 𝒞_P(E) × 𝒞_Q(E) → ℂ` pairs plane classes of `E` with LINE classes of `E`, the latter standing
for the PLANE classes of `E*` through `φ`.  Here `lineLitEquiv : H²(line; E) ≃ₗ H²(plane; E*)` (`Θ ∘ toPlaneStar`), its restriction
`innerLineLitEquiv` to inner classes, the literal plane pairing `facePairingPLit : 𝒞_P(E) × 𝒞_P(E*) → ℂ`, and
`facePairingPLit_eq_traceValuePLit`: it is the trace formula with the evaluation pairing `E ⊗ E* → ℂ`, for any representatives and edge primitive.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.EisensteinDual

variable (n : ℕ)

/-- Value of the model line cocycle `fromPlaneStar (Θ⁻¹ y'')` at dual tuples and the dual of a plane flag. -/
theorem fromPlane_val
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane))
    (a b c : RationalGL3) (F : Flags .plane) :
    (fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) y'')).val.val
        ![dualInvolution a, dualInvolution b, dualInvolution c] (dualPlaneFlag F) =
      (thetaModelEquiv n).symm (y''.val.val ![a, b, c] F) := by
  change (thetaXInvCocycles n (Flags .plane) y'').val.val
      (fun i => dualInvolution ((![dualInvolution a, dualInvolution b, dualInvolution c] : Fin 3 → RationalGL3) i))
      (dualFlag (dualPlaneFlag F)) = _
  rw [phi_vec3_inv, dualFlag_dualPlaneFlag]
  rfl

/-- Local value of the plane face-pairing trace for the literal dual `E*` (evaluation instead of the apolar pairing). -/
def litPlaneValue {ι L P : Type} [Fintype ι] [Fintype L] [Fintype P] [DecidableEq L] [DecidableEq P]
    (Θ : TraceData ι L P) (v : P)
    (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)) : ℂ :=
  (∑ i ∈ Finset.univ.filter (fun i => Θ.planeOf i = v),
      Finsupp.linearCombination ℂ (fun x => (y''.val.val ![x 1, x 2, x 3] (Θ.planeRep v))
        (w.val ![x 0, x 1] (Θ.edge i))) (Θ.chain i)) -
    Finsupp.linearCombination ℂ (fun x => (y''.val.val ![x 2, x 3, x 4] (Θ.planeRep v))
      (z.val.val ![x 0, x 1, x 2] (Θ.planeRep v))) (Θ.planeFill v)

/-- The literal plane trace pairing: sum of the local values at the two plane cusps. -/
def traceValuePLit (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)) : ℂ :=
  ∑ v : Fin 2, litPlaneValue n traceDataL2 v z w y''

theorem traceValuePLit_eq (z : MaximalCycles n trivialCharacter .plane) (w : EdgeCochains n trivialCharacter 1)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)) :
    traceValuePLit n z w y'' =
      traceValueP z w (fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) y'')) := by
  unfold traceValuePLit traceValueP
  refine Finset.sum_congr rfl fun v _ => ?_
  unfold litPlaneValue planeValueP
  have e1 : ∀ i, (fun x : Fin 4 → RationalGL3 => (y''.val.val ![x 1, x 2, x 3] (traceDataL2.planeRep v))
        (w.val ![x 0, x 1] (traceDataL2.edge i))) =
      fun x => (dualityDataP n trivialCharacter).B (w.val ![x 0, x 1] (traceDataL2.edge i))
        ((fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) y'')).val.val
          ![(dualityDataP n trivialCharacter).φ (x 1), (dualityDataP n trivialCharacter).φ (x 2),
            (dualityDataP n trivialCharacter).φ (x 3)]
          ((dualityDataP n trivialCharacter).dualFlag (traceDataL2.planeRep v))) := by
    intro i
    funext x
    change _ = dualPairing n _ _
    erw [fromPlane_val, pairing_literal]
  have e2 : (fun x : Fin 5 → RationalGL3 => (y''.val.val ![x 2, x 3, x 4] (traceDataL2.planeRep v))
        (z.val.val ![x 0, x 1, x 2] (traceDataL2.planeRep v))) =
      fun x => (dualityDataP n trivialCharacter).B (z.val.val ![x 0, x 1, x 2] (traceDataL2.planeRep v))
        ((fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) y'')).val.val
          ![(dualityDataP n trivialCharacter).φ (x 2), (dualityDataP n trivialCharacter).φ (x 3),
            (dualityDataP n trivialCharacter).φ (x 4)]
          ((dualityDataP n trivialCharacter).dualFlag (traceDataL2.planeRep v))) := by
    funext x
    change _ = dualPairing n _ _
    erw [fromPlane_val, pairing_literal]
  simp only [e1, e2]

section Strata

/-- `E`-line cocycles to `E*`-plane cocycles: `Θ ∘ toPlaneStar`. -/
def lineToLitCocycles : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) :=
  (thetaXCocycles n (Flags .plane)) ∘ₗ (toPlaneStar (rationalCoefficientComponent n trivialCharacter))

/-- `E*`-plane cocycles to `E`-line cocycles: `fromPlaneStar ∘ Θ⁻¹`. -/
def litToLineCocycles : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) →ₗ[ℂ]
    cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) :=
  (fromPlaneStar (rationalCoefficientComponent n trivialCharacter)) ∘ₗ (thetaXInvCocycles n (Flags .plane))

theorem litToLine_lineToLit (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    litToLineCocycles n (lineToLitCocycles n z) = z := by
  have e : thetaXInvCocycles n (Flags .plane) (thetaXCocycles n (Flags .plane) (toPlaneStar (rationalCoefficientComponent n trivialCharacter) z)) = toPlaneStar (rationalCoefficientComponent n trivialCharacter) z := by
    apply Subtype.ext
    apply Subtype.ext
    funext x F
    exact congrFun (thetaFunInv_thetaFun n (Flags .plane) ((toPlaneStar (rationalCoefficientComponent n trivialCharacter) z).val.val x)) F
  change fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) (thetaXCocycles n (Flags .plane) (toPlaneStar (rationalCoefficientComponent n trivialCharacter) z))) = z
  rw [e, fromPlaneStar_toPlaneStar]

theorem lineToLit_litToLine (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)) :
    lineToLitCocycles n (litToLineCocycles n z) = z := by
  change thetaXCocycles n (Flags .plane) (toPlaneStar (rationalCoefficientComponent n trivialCharacter) (fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) z))) = z
  have e := toPlaneStar_fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) z)
  rw [e]
  apply Subtype.ext
  apply Subtype.ext
  funext x F
  exact congrFun (thetaFun_thetaFunInv n (Flags .plane) (z.val.val x)) F

theorem lineToLit_boundary
    (s : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) 1) :
    lineToLitCocycles n (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) s) =
      boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)
        (thetaXCochains n (Flags .plane)
          1 (transportCochains (rationalCoefficientComponent n trivialCharacter)
            (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul 1 s)) := by
  have h := transportCocycles_boundaryMap (rationalCoefficientComponent n trivialCharacter)
    (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul s
  exact (congrArg (thetaXCocycles n (Flags .plane)) h).trans
    (coeffCocycles_boundaryMap rationalLevel _ _ _ _ _)

/-- Induced map on cohomology of the strata: line classes of `E` to plane classes of `E*`. -/
def lineToLitH2 : StratumH2 n trivialCharacter .line →ₗ[ℂ] StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .plane :=
  Submodule.mapQ _ _ (lineToLitCocycles n) (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (lineToLit_boundary n s).symm⟩)

theorem litToLine_boundary
    (s : cochains rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) 1) :
    litToLineCocycles n (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) s) =
      boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (transportCochains (dualRep (rationalCoefficientComponent n trivialCharacter))
          (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualFlag dualFlag_smul 1
          (thetaXInvCochains n (Flags .plane) 1 s)) := by
  have h1 : thetaXInvCocycles n (Flags .plane)
      (boundaryMap rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) s) =
      boundaryMap rationalLevel (functionRepresentation (dualRep (rationalCoefficientComponent n trivialCharacter)) (Flags .plane))
        (thetaXInvCochains n (Flags .plane) 1 s) :=
    coeffCocycles_boundaryMap rationalLevel _ _ _ _ _
  have h := transportCocycles_boundaryMap (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualFlag dualFlag_smul
    (thetaXInvCochains n (Flags .plane) 1 s)
  exact (congrArg (fromPlaneStar (rationalCoefficientComponent n trivialCharacter)) h1).trans h

def litToLineH2 : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .plane →ₗ[ℂ] StratumH2 n trivialCharacter .line :=
  Submodule.mapQ _ _ (litToLineCocycles n) (fun x hx => by
    obtain ⟨s, rfl⟩ := hx
    exact ⟨_, (litToLine_boundary n s).symm⟩)

/-- **The strata isomorphism** `H²(Γ, flags_Q; E) ≃ H²(Γ, flags_P; E*)`, `Θ ∘ (c ↦ c∘φ)`. -/
def lineLitEquiv : StratumH2 n trivialCharacter .line ≃ₗ[ℂ] StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .plane :=
  LinearEquiv.ofLinearMap (lineToLitH2 n) (litToLineH2 n)
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      change (lineToLitH2 n) ((litToLineH2 n) (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
      simp only [litToLineH2, lineToLitH2, Submodule.mapQ_apply]
      rw [lineToLit_litToLine])
    (by
      apply LinearMap.ext
      intro x
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      change (litToLineH2 n) ((lineToLitH2 n) (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
      simp only [litToLineH2, lineToLitH2, Submodule.mapQ_apply]
      rw [litToLine_lineToLit])

theorem lineLitEquiv_mk (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)) :
    lineLitEquiv n (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line) z) =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)
        (lineToLitCocycles n z) := rfl

theorem lineLitEquiv_symm_mk (z : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane)) :
    (lineLitEquiv n).symm (classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) z) =
      classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
        (litToLineCocycles n z) := rfl

theorem lineLit_inner (ξ : StratumH2 n trivialCharacter .line) (hξ : InnerBoundary n trivialCharacter .line ξ) :
    InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .plane (lineLitEquiv n ξ) := by
  obtain ⟨y0, hy0, u, hu⟩ := hξ
  subst hy0
  rw [lineLitEquiv_mk]
  have h1 := edgeExact_transport (rationalCoefficientComponent n trivialCharacter)
    (dualRep (rationalCoefficientComponent n trivialCharacter)) (fun _ => rfl) dualPlaneFlag dualPlaneFlag_smul
    (endpoint .line) (endpoint .plane) (fun e => (endpoint_line_dualEdge e).symm) y0 u hu
  refine inner_theta n .plane (toPlaneStar (rationalCoefficientComponent n trivialCharacter) y0)
    (toEdgeStar (rationalCoefficientComponent n trivialCharacter) u) (fun x e => h1 x e)

theorem litLine_inner
    (η : StratumH2Rep (rationalCoefficientComponent n trivialCharacter).dual .plane)
    (hη : InnerBoundaryRep (rationalCoefficientComponent n trivialCharacter).dual .plane η) :
    InnerBoundary n trivialCharacter .line ((lineLitEquiv n).symm η) := by
  obtain ⟨z', hz', u', hu'⟩ := hη
  subst hz'
  rw [lineLitEquiv_symm_mk]
  obtain ⟨z0, hz0, u0, hu0⟩ := inner_theta_inv n .plane z' u' hu'
  have h1 := edgeExact_transport (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualFlag dualFlag_smul
    (endpoint .plane) (endpoint .line) (fun e => (endpoint_plane_dualEdge e).symm) z0 u0 hu0
  refine ⟨fromPlaneStar (rationalCoefficientComponent n trivialCharacter) z0, ?_,
    transportCochains (dualRep (rationalCoefficientComponent n trivialCharacter))
      (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualEdge dualEdge_smul 1 u0,
    fun x e => h1 x e⟩
  exact classOf_transport (dualRep (rationalCoefficientComponent n trivialCharacter))
    (rationalCoefficientComponent n trivialCharacter) (dualRep_dualRep_apply _) dualFlag dualFlag_smul hz0

/-- The inner (mixed cuspidal) line classes of `E` correspond to the inner plane classes of `E*`. -/
def innerLineLitEquiv : innerClasses n .line ≃ₗ[ℂ]
    innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane :=
  LinearEquiv.ofSubmodules (lineLitEquiv n) (innerClasses n .line)
    (innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane) (by
      ext η
      rw [Submodule.mem_map_equiv]
      constructor
      · intro h
        have h' := lineLit_inner n ((lineLitEquiv n).symm η) h
        rwa [LinearEquiv.apply_symm_apply] at h'
      · intro h
        exact litLine_inner n η h)

/-- **The face pairing `⟨ , ⟩_P` for the literal dual `E*`**: `𝒞_P(E) × 𝒞_P(E*) → ℂ`. -/
def facePairingPLit : innerClasses n .plane →ₗ[ℂ]
    innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane →ₗ[ℂ] ℂ :=
  LinearMap.compl₂ (facePairingP n)
    ((innerLineLitEquiv n).symm : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane →ₗ[ℂ] innerClasses n .line)

/-- Representative independence for the literal plane pairing: it is the literal trace `traceValuePLit z w y''` on any representatives. -/
theorem facePairingPLit_eq_traceValuePLit (b : innerClasses n .plane)
    (η : innerClassesRep (rationalCoefficientComponent n trivialCharacter).dual .plane)
    (z : MaximalCycles n trivialCharacter .plane)
    (hz : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .plane) z = b.1)
    (w : EdgeCochains n trivialCharacter 1) (hw : EdgePrimitiveP z w)
    (y'' : cocycles rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane))
    (hy : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter).dual .plane) y'' = η.1) :
    facePairingPLit n b η = traceValuePLit n z w y'' := by
  have hξ : InnerBoundary n trivialCharacter .line ((lineLitEquiv n).symm η.1) := litLine_inner n η.1 η.2
  have hclass : classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n trivialCharacter) .line)
      (litToLineCocycles n y'') = (lineLitEquiv n).symm η.1 := by
    rw [← hy]
    exact (lineLitEquiv_symm_mk n y'').symm
  have h := pairingValue_eqP b.2 hξ hz hw hclass
  have e0 : facePairingPLit n b η = pairingValueP n b.1 ((lineLitEquiv n).symm η.1) := rfl
  have e : litToLineCocycles n y'' =
      fromPlaneStar (rationalCoefficientComponent n trivialCharacter) (thetaXInvCocycles n (Flags .plane) y'') := rfl
  rw [e0, h, traceValuePLit_eq, e]

end Strata

end TernaryPeriodPolynomials.Argument.EisensteinDual
