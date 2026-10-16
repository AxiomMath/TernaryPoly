module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Face.Pairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.CornerChain

@[expose] public section


/-!
# Corner evaluation of the cone pairing of two line data, for arbitrary coefficient modules

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`, and Lemma C.2.

For the cone cochains `(w, z, 0)`, `(w', z', 0)` of two line data (resp. `(-w, 0, z)` of plane data), the cone pairing on a coinvariant cycle `v` is the
evaluation on the corner chain `pA 3 v` of the flag 3-cochain `w ∪ (z'|flags) - γ|flags`, where `γ` is any primitive of the cup product `z ∪ z'` on the line
complex (resp. the plane analogue).  The corner chain is a coinvariant 3-cycle of the flag complex whose images in the line and plane complexes pair to zero with
every cocycle (`PushCone.corner_cycle`, `corner_line`, `corner_plane`).  This is the generic-coefficient version of the `Glue.pair_lineLift`.
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPeriodPolynomials.Argument.GammaNStokes
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein
open TernaryPoly.SymmetricSpaceBoundaryFull

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (v : coneR.X 4)

/-- **Corner evaluation for two line data.**  If the cup product `z ∪ z'` of the line cocycles is the coboundary of a 3-cochain `γ` of the
line complex, the cone pairing of the two cone cochains `(w, z, 0)`, `(w', z', 0)` on a coinvariant cycle `v` is the evaluation, on the
corner chain `pA 3 v` of `v`, of the flag 3-cochain `w ∪ (z'|_flags) - γ|_flags`. -/
theorem LineDatum.conePair_eq_corner (d : LineDatum W) (e : LineDatum W') (hv : IsCoinvCycle v)
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    conePair π v d.cone e.cone =
      (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) ≫ π) -
        flagLineHom.hom.f 3 ≫ γ).hom ((modelPush.pA 3).hom v) := by
  have hL : (resLine.complex).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ d.cone) ⊗ₘ (modelPush.iL 2 ≫ e.cone)) ≫ π := by
    unfold LineDatum.cone
    rw [lineCone_line, lineCone_line]
    exact hγ
  have hP : (resPlane.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ d.cone) ⊗ₘ (modelPush.iP 2 ≫ e.cone)) ≫ π := by
    unfold LineDatum.cone
    rw [lineCone_plane, lineCone_plane, PushCone.zero_tensorHom', zero_comp, comp_zero]
    simp
  have key := modelPush.pair_cycle (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) d.cone e.cone π v hv γ 0 hL hP
  unfold conePair
  refine Eq.trans key ?_
  have e1 : modelPush.iA 1 ≫ d.cone = d.w := lineCone_corner _ _
  have e2 : modelPush.iL 2 ≫ e.cone = e.z := lineCone_line _ _
  have e3 : modelPush.iP 2 ≫ d.cone = 0 := lineCone_plane _ _
  rw [e1, e2, e3]
  simp [PushCone.zero_tensorHom']

/-- **Corner evaluation for two plane data** (cone cochains `(-w, 0, z)`, `(-w', 0, z')`). -/
theorem PlaneDatum.conePair_eq_corner (d : PlaneDatum W) (e : PlaneDatum W') (hv : IsCoinvCycle v)
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    conePair π v d.cone e.cone =
      (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 2 1 3 rfl ≫ ((flagPlaneHom.hom.f 2 ≫ d.z) ⊗ₘ (-e.w)) ≫ π) +
        flagPlaneHom.hom.f 3 ≫ γ).hom ((modelPush.pA 3).hom v) := by
  have hL : (resLine.complex).d 4 3 ≫ (0 : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫
        ((modelPush.iL 2 ≫ d.cone) ⊗ₘ (modelPush.iL 2 ≫ e.cone)) ≫ π := by
    unfold PlaneDatum.cone
    rw [planeCone_line, planeCone_line, PushCone.zero_tensorHom', zero_comp, comp_zero]
    simp
  have hP : (resPlane.complex).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫
        ((modelPush.iP 2 ≫ d.cone) ⊗ₘ (modelPush.iP 2 ≫ e.cone)) ≫ π := by
    unfold PlaneDatum.cone
    rw [planeCone_plane, planeCone_plane]
    exact hγ
  have key := modelPush.pair_cycle (nerveDiagSystem Γ6 RationalGL3 Flag) (nerveDiagSystem Γ6 RationalGL3 Line)
    (nerveDiagSystem Γ6 RationalGL3 Plane) d.cone e.cone π v hv 0 γ hL hP
  unfold conePair
  refine Eq.trans key ?_
  have e1 : modelPush.iA 1 ≫ e.cone = -e.w := planeCone_corner _ _
  have e2 : modelPush.iL 2 ≫ e.cone = 0 := planeCone_line _ _
  have e3 : modelPush.iP 2 ≫ d.cone = d.z := planeCone_plane _ _
  rw [e1, e2, e3]
  simp [PushCone.tensorHom_zero']

/-- **Independence of the primitive.**  Changing `γ` by a cocycle `ξ` of the line complex changes the flag 3-cochain `w ∪ z'|flags - γ|flags` by
`flagLine^* ξ`, which vanishes on the corner chain of every coinvariant cycle.  (This is why the evaluation, and not each local term, is the invariant.) -/
theorem corner_eval_indep_line (hv : IsCoinvCycle v) (ξ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hξ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ ξ = 0) :
    (flagLineHom.hom.f 3 ≫ ξ).hom ((modelPush.pA 3).hom v) = 0 :=
  modelPush.corner_line hv ξ hξ

/-- The same for the plane complex. -/
theorem corner_eval_indep_plane (hv : IsCoinvCycle v) (ξ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hξ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ ξ = 0) :
    (flagPlaneHom.hom.f 3 ≫ ξ).hom ((modelPush.pA 3).hom v) = 0 :=
  modelPush.corner_plane hv ξ hξ

/-- Two primitives of the same cup product give the same corner evaluation (consequence of `LineDatum.conePair_eq_corner`). -/
theorem LineDatum.corner_eval_eq (d : LineDatum W) (e : LineDatum W') (hv : IsCoinvCycle v)
    (γ γ' : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (hγ' : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ' =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) :
    (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) ≫ π) -
        flagLineHom.hom.f 3 ≫ γ).hom ((modelPush.pA 3).hom v) =
    (((nerveDiagSystem Γ6 RationalGL3 Flag).Δ 1 2 3 rfl ≫ (d.w ⊗ₘ (flagLineHom.hom.f 2 ≫ e.z)) ≫ π) -
        flagLineHom.hom.f 3 ≫ γ').hom ((modelPush.pA 3).hom v) :=
  (LineDatum.conePair_eq_corner π v d e hv γ hγ).symm.trans (LineDatum.conePair_eq_corner π v d e hv γ' hγ')

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
