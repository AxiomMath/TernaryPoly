module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Face.PairBridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Final
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.MixedEdge

@[expose] public section


/-!
# The fibre-integration identity (M3) as a single proposition, and `FaceFactorisation6` from M3, M1, (B) and the constants of step (iv)

Formalized by Claude Sonnet 5.5.
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

/-- **Evaluation data on the cohomology of the flag groups** (the output of step (ii)/(M1)): classes `G o` spanning `H³(Stab o.out; ℚ)` (S1's `H3FlagData`) and the coordinate functionals `lam o` with `lam o (G o) = 1`. -/
structure FlagEval where
  D : H3FlagData
  lam : ∀ o : labelOrbits Γ6 Flag, groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype Wq) 3 →ₗ[ℚ] ℚ
  lam_G : ∀ o, lam o (D.G o) = 1

/-- The flag class (coordinate at the flag orbit `o`) of the corner cocycle of two line data. -/
def lineFlagClass {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (o : labelOrbits Γ6 Flag) :
    groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype Wq) 3 :=
  (faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out (fun g => g.2) 3).hom
    (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (lineFlagCochain π d.w e.z γ)
      (lineFlagCochain_cocycle π d e γ hγ))

/-- The flag class of the corner cocycle of two plane data. -/
def planeFlagClass {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (o : labelOrbits Γ6 Flag) :
    groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype Wq) 3 :=
  (faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out (fun g => g.2) 3).hom
    (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (planeFlagCochain π d.z e.w γ)
      (planeFlagCochain_cocycle π d e γ hγ))

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
def M3Line (E : FlagEval) : Prop :=
  ∃ κ : LineFaces 6 → ℚ, (∀ i, κ i ≠ 0) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V) (i : LineFaces 6) (x : lineMixedSub ρ i) (y : lineMixedSub ρ.dual i)
      (d : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : LineDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
      (_ : d.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i))) (_ : e.IsOn (labelOrbit Γ6 Line (lineFacesEquivOrbits i)))
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
      ∑ o, E.lam o (lineFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ o) = κ i * r (can6 ρ i x y)

/-- **(M3), planes.** -/
def M3Plane (E : FlagEval) : Prop :=
  ∃ κ : PlaneFaces 6 → ℚ, (∀ i, κ i ≠ 0) ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (gammaN 6) V) (i : PlaneFaces 6) (x : planeMixedSub ρ i) (y : planeMixedSub ρ.dual i)
      (d : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ))) (e : PlaneDatum (qRep (MonoidHom.id Γ6) (rep6 ρ).dual))
      (_ : d.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i))) (_ : e.IsOn (labelOrbit Γ6 Plane (planeFacesEquivOrbits i)))
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
      ∑ o, E.lam o (planeFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ o) = κ i * r (can6P ρ i x y)

theorem flagPhi_eq_smul_lam (E : FlagEval) (Λ : ℚ) (hΛ : ∀ (o : labelOrbits Γ6 Flag) (r : ℚ), flagPhi o (r • E.D.G o) = Λ * r)
    (o : labelOrbits Γ6 Flag) (y : groupCohomology (Rep.res (stabilizer Γ6 o.out).subtype Wq) 3) :
    flagPhi o y = Λ * E.lam o y := by
  obtain ⟨s, rfl⟩ := E.D.span o y
  rw [hΛ, map_smul, E.lam_G, smul_eq_mul, mul_one]

theorem rat_cast_mul_apply (r : ℂ →ₗ[ℚ] ℚ) (q : ℚ) (z : ℂ) : r ((q : ℂ) * z) = q * r z := by
  have : (q : ℂ) * z = q • z := (Rat.smul_def q z).symm
  rw [this, map_smul, smul_eq_mul]

/-- **`FaceFactorisation6` (a′) from the fibre-integration identity M3, the evaluation data (M1), the sum-zero hypotheses (B) and S1's constants (iv).**  The constants are `c i = Λ κ_L i`, `d i = Λ κ_P i`
(`κ_L i`, `κ_P i` from M3) with `Λ` the universal coefficient of the corner functional against the fundamental classes. -/
theorem faceFactorisation6_of_M3 (E : FlagEval) (F : ConjFrames) (hL : LineImageSumZero E.D F) (hP : PlaneImageSumZero E.D F)
    (h3L : M3Line E) (h3P : M3Plane E) : FaceFactorisation6 := by
  obtain ⟨κL, hκL, hLine⟩ := h3L
  obtain ⟨κP, hκP, hPlane⟩ := h3P
  obtain ⟨-, -, Λ, hΛ0, -, -, hΛ⟩ := face_constants hL hP
  refine ⟨fun i => ((Λ * κL i : ℚ) : ℂ), fun i => ((Λ * κP i : ℚ) : ℂ), fun i => ?_, fun i => ?_, ?_⟩
  · show ((Λ * κL i : ℚ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero hΛ0 (hκL i)
  · show ((Λ * κP i : ℚ) : ℂ) ≠ 0
    exact_mod_cast mul_ne_zero hΛ0 (hκP i)
  · intro V _ _ _ _ _ ρ
    refine ⟨fun i x y => ?_, fun i x y => ?_⟩
    · obtain ⟨d, e, hd, he, hdc, hec⟩ := lineFace_exists_lifts ρ i x.1 y.1 x.2 y.2
      rw [← sub_eq_zero]
      apply eq_zero_of_forall_rat_functional
      intro r
      obtain ⟨γ, hγ⟩ := exists_line_primitive
        ((nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r))
        (cup_cocycle (nerveDiagSystem Γ6 RationalGL3 Line) d.z d.hz e.z e.hz _)
      have h1 := lineFacePairM_functional ρ i x.1 y.1 d e hd he hdc hec r γ hγ
      have h2 := hLine V ρ i x y d e hd he hdc hec r γ hγ
      rw [map_sub, rat_cast_mul_apply, h1]
      have h3 : ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (lineFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.w e.z γ)
            (lineFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ))) =
          Λ * ∑ o, E.lam o (lineFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ o) := by
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
      have h1 := planeFacePairM_functional ρ i x.1 y.1 d e hd he hdc hec r γ hγ
      have h2 := hPlane V ρ i x y d e hd he hdc hec r γ hγ
      rw [map_sub, rat_cast_mul_apply, h1]
      have h3 : ∑ o, flagPhi o ((faceCoord (stabilizer Γ6 o.out) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) o.out
          (fun g => g.2) 3).hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
            (planeFlagCochain (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d.z e.w γ)
            (planeFlagCochain_cocycle (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ))) =
          Λ * ∑ o, E.lam o (planeFlagClass (evalC (MonoidHom.id Γ6) (rep6 ρ) ≫ rHom r) d e γ hγ o) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun o _ => flagPhi_eq_smul_lam E Λ hΛ o _
      rw [h3, h2]
      ring

end M3

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
