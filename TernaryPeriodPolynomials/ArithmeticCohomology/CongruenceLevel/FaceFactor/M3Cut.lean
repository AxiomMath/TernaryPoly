module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.M3Def

@[expose] public section


/-!
# M3 with the cut primitive, and `FaceFactorisation6` from it

Formalized by Claude Sonnet 5.5.

`M3LineC`, `M3PlaneC`: the fibre-integration identity for the primitive `γ' = cut_S ∘ γ` supported on the orbit `S` of the face (the form in which the flag sum is computed: `GeneralReduction.lineSum_general`).
`faceFactorisation6_of_M3C`: `FaceFactorisation6` follows from `M3LineC`, `M3PlaneC` exactly as from `M3Line`, `M3Plane`, because the functional identities `lineFacePairM_functional` hold for every primitive, in particular the cut one.
-/

open CategoryTheory Limits MonoidalCategory
open scoped MatrixGroups
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly.EquivariantSingularSmall TernaryPoly.BoundaryFaceResolutionComparison
open GeneralEisenstein
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section M3

open TernaryPeriodPolynomials.Argument.GammaNFacesFull
open TernaryPeriodPolynomials.Argument.GammaNFaces
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.ConvergenceC4
open TernaryPeriodPolynomials.Argument.GammaNParabolicPD
open TernaryPeriodPolynomials.Argument.GammaNStokes.LevelChange

/-- **(M3), lines: the fibre-integration identity.**  There are nonzero rationals `κ i` (one per face), independent of the coefficients, such that for every finite-dimensional coefficient module `ρ` of `Γ(6)`, every line
face `i`, all mixed classes `x`, `y`, all lifts `d`, `e` (supported on the orbit of `i`), every rational functional `r` of `ℂ` and EVERY primitive `γ` of `d.z ∪ e.z` (for `evalC ≫ rHom r`), the sum over all flag orbits of the
coordinates `lam o` of the flag classes of the corner cocycle equals `κ i · r (can6 ρ i x y)`, where `can6` is S2's canonical pairing `facePairingCan` of the Hochschild-Serre edges of `x`, `y`. -/
def M3LineAt (E : FlagEval) (κ : LineFaces 6 → ℚ) : Prop :=
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i)
      (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
      (hd : d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i))) (he : e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
      (_ : d.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) x.1))
      (_ : e.coord (lineFacesEquivOrbits i) =
        faceTauQ (fun i : LineFaces 6 => lineFacesEquivOrbits i) (fun i => lineOf i.rep) lineOf_rep_mem
          (fun i => ↥(gammaNQAt 6 i.rep)) (fun i => lineEmb i.rep) (fun i => lineEmb_injective i.rep)
          (fun i => lineEmb_range i.rep) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNQAt_le_gammaN 6 i.rep hp)) y.1))
      (r : ℂ →ₗ[ℚ] ℚ) (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
      (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
        (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)),
      ∑ o, E.lam o (lineFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e
        (cutHom Γ6 RationalGL3 Line (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ)
        (cutγ_line_primitive _ d e γ hγ _ (labelOrbit_invariant _) hd he) o) = κ i * r (can6 ρ i x y)

/-- **(M3), planes.** -/
def M3PlaneAt (E : FlagEval) (κ : PlaneFaces 6 → ℚ) : Prop :=
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i)
      (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
      (hd : d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i))) (he : e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
      (_ : d.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ) i
          (cmpH2 ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) x.1))
      (_ : e.coord (planeFacesEquivOrbits i) =
        faceTauQ (fun i : PlaneFaces 6 => planeFacesEquivOrbits i) (fun i => planeOf (planeFaceRepr i)) planeOf_rep_mem
          (fun i => ↥(gammaNPAt 6 (planeFaceRepr i))) (fun i => planeEmb (planeFaceRepr i)) (fun i => planeEmb_injective (planeFaceRepr i))
          (fun i => planeEmb_range (planeFaceRepr i)) (rep6 ρ).dual i
          (cmpH2Dual ρ (Subgroup.inclusion (fun _ hp => gammaNPAt_le_gammaN 6 (planeFaceRepr i) hp)) y.1))
      (r : ℂ →ₗ[ℚ] ℚ) (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
      (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
        (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r)),
      ∑ o, E.lam o (planeFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e
        (cutHom Γ6 RationalGL3 Plane (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ)
        (cutγ_plane_primitive _ d e γ hγ _ (labelOrbit_invariant _) hd he) o) = κ i * r (can6P ρ i x y)

/-- (M3), lines, with the constants left unspecified (nonzero rationals, one per face). -/
def M3LineC (E : FlagEval) : Prop := ∃ κ : LineFaces 6 → ℚ, (∀ i, κ i ≠ 0) ∧ M3LineAt E κ

/-- (M3), planes, with the constants left unspecified. -/
def M3PlaneC (E : FlagEval) : Prop := ∃ κ : PlaneFaces 6 → ℚ, (∀ i, κ i ≠ 0) ∧ M3PlaneAt E κ

/-- **The factorisation of the cone pairings with explicit constants**: from `M3LineAt E κL`, `M3PlaneAt E κP`, (B_L), (B_P) and S1's universal coefficient `Λ ≠ 0`:
`lineFacePairM = Λ κ_L(i) · can6` and `planeFacePairM = Λ κ_P(i) · can6P`. -/
theorem factorisation_of_M3At (E : FlagEval) (F : ConjFrames) (hL : LineImageSumZero E.D F) (hP : PlaneImageSumZero E.D F)
    (κL : LineFaces 6 → ℚ) (κP : PlaneFaces 6 → ℚ) (hLine : M3LineAt E κL) (hPlane : M3PlaneAt E κP) :
    ∃ Λ : ℚ, Λ ≠ 0 ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ (gammaN 6) V),
        (∀ (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i),
          lineFacePairM ρ i x.1 y.1 = ((Λ * κL i : ℚ) : ℂ) * can6 ρ i x y) ∧
        (∀ (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i),
          planeFacePairM ρ i x.1 y.1 = ((Λ * κP i : ℚ) : ℂ) * can6P ρ i x y) := by
  obtain ⟨-, -, Λ, hΛ0, -, -, hΛ⟩ := face_constants hL hP
  refine ⟨Λ, hΛ0, ?_⟩
  intro V _ _ _ _ _ ρ
  refine ⟨fun i x y => ?_, fun i x y => ?_⟩
  · obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x.1 y.1 x.2 y.2
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_rat_functional
    intro r
    obtain ⟨γ, hγ⟩ := exists_line_primitive
      ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r))
      (cup_cocycle (nerveDiagSystem Γ6 RationalGL3 Line) d.z d.hz e.z e.hz _)
    have hγ' := cutγ_line_primitive (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ
      (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) hd he
    have h1 := lineFacePairM_functional ρ i x.1 y.1 d e hd he hdc hec r _ hγ'
    have h2 := hLine V ρ i x y d e hd he hdc hec r γ hγ
    rw [map_sub, rat_cast_mul_apply, h1]
    have h3 : ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (lineFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.w e.z
            (cutHom Γ6 RationalGL3 Line (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ))
          (lineFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e _ hγ'))) =
        Λ * ∑ o, E.lam o (lineFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e
          (cutHom Γ6 RationalGL3 Line (labelOrbit Γ6 Line (lineFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ) hγ' o) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => flagPhi_eq_smul_lam E Λ hΛ o _
    rw [h3, h2]
    ring
  · obtain ⟨d, e, hd, he, hdc, hec⟩ := planeFace_exists_lifts ρ i x.1 y.1 x.2 y.2
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_rat_functional
    intro r
    obtain ⟨γ, hγ⟩ := exists_plane_primitive
      ((nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r))
      (cup_cocycle (nerveDiagSystem Γ6 RationalGL3 Plane) d.z d.hz e.z e.hz _)
    have hγ' := cutγ_plane_primitive (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ
      (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) hd he
    have h1 := planeFacePairM_functional ρ i x.1 y.1 d e hd he hdc hec r _ hγ'
    have h2 := hPlane V ρ i x y d e hd he hdc hec r γ hγ
    rw [map_sub, rat_cast_mul_apply, h1]
    have h3 : ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
        (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
          (planeFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.z e.w
            (cutHom Γ6 RationalGL3 Plane (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ))
          (planeFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e _ hγ'))) =
        Λ * ∑ o, E.lam o (planeFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e
          (cutHom Γ6 RationalGL3 Plane (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)) (labelOrbit_invariant _) 3 ≫ γ) hγ' o) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun o _ => flagPhi_eq_smul_lam E Λ hΛ o _
    rw [h3, h2]
    ring


/-- **`FaceFactorisation6` (a′) from the fibre-integration identity M3, the evaluation data (M1), the sum-zero hypotheses (B) and S1's constants (iv).**  The constants are `c i = Λ κ_L i`, `d i = Λ κ_P i`
(`κ_L i`, `κ_P i` from M3) with `Λ` the universal coefficient of the corner functional against the fundamental classes. -/
theorem faceFactorisation6_of_M3C (E : FlagEval) (F : ConjFrames) (hL : LineImageSumZero E.D F) (hP : PlaneImageSumZero E.D F)
    (h3L : M3LineC E) (h3P : M3PlaneC E) : FaceFactorisation6 := by
  obtain ⟨κL, hκL, hLine⟩ := h3L
  obtain ⟨κP, hκP, hPlane⟩ := h3P
  obtain ⟨Λ, hΛ0, h⟩ := factorisation_of_M3At E F hL hP κL κP hLine hPlane
  refine ⟨fun i => ((Λ * κL i : ℚ) : ℂ), fun i => ((Λ * κP i : ℚ) : ℂ), fun i => ?_, fun i => ?_,
    fun V _ _ _ _ _ ρ => h V ρ⟩
  · show ((Λ * κL i : ℚ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero hΛ0 (hκL i)
  · show ((Λ * κP i : ℚ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero hΛ0 (hκP i)

end M3

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
