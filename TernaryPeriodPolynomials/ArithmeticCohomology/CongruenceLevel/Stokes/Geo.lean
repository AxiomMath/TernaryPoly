module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.ComplexStokes

@[expose] public section


/-!
# The Stokes cycle together with its geometric comparison data

Formalized by Claude Sonnet 5.5.

`cone_stokes_complex` produces a coinvariant cycle `Ω` of the model cone but forgets how it was obtained.  The cycle comes from `exists_pairGeo`: together with it there are
a carried comparison `Ψ : coneR ⟶ boundaryChains` (a quasi-isomorphism over the augmentation), a nonzero rational `κ` such that the cone pairing at `Ω` of cone cocycles
pulling back along `Ψ` to boundary cocycles is `κ` times their geometric pairing (`PairGeo Ψ Ω κ`), and a nonzero `c₀` comparing the level trace with the evaluation on the corner chain
of `Ω`.  These are exactly the inputs of the line and plane glue `LineGlue Ψ (κ c₀)`, `PlaneGlue Ψ (-(κ c₀))` (`glue_of_pairGeo`).

Here `GeoData Ω` packages this information, `cone_stokes_geo` is `cone_stokes_complex` for a cycle with `GeoData`, and `Ω` is then fixed as `stokesCycle` (in `OrbitStokes`).
-/

open CategoryTheory Limits MonoidalCategory
open TernaryPeriodPolynomials.Argument.TopHomology
open TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison
open TernaryPeriodPolynomials.Argument.FacePairingFull.CapCompat
open TernaryPoly.SingularLocalDuality (dualRepresentation dualValue)
open TernaryPoly.SymmetricSpaceBoundaryMV (Flag)
open TernaryPoly.OrdinaryIncidence (Line Plane)
open GeneralEisenstein
open TernaryPeriodPolynomials.Argument.FacePairingFull.Glue
open TernaryPoly TernaryPoly.IntegralGL3Congruence
open TernaryPoly.SymmetricSpaceBoundaryFull
open TernaryPoly.SymmetricSpaceBoundaryIncidenceHomology (boundaryChains ambient)
open TernaryPoly.BoundaryFaceResolutionComparison
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.Argument.CoinvScalar
open TernaryPeriodPolynomials.Duality
open TernaryPeriodPolynomials.BoundaryDuality.TraceRepresentatives

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNStokes

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

/-- **The geometric comparison data of a coinvariant cycle `Ω` of the model cone**: a carried comparison `Ψ` to the boundary chains (quasi-isomorphism over the augmentation), a nonzero
rational `κ` with `PairGeo Ψ Ω κ` and a nonzero complex `c₀` comparing the level trace with the corner evaluation of `Ω`. -/
def GeoData (Ω : coneR.X 4) : Prop :=
  ∃ (Ψ : coneR ⟶ boundaryChains) (κ : ℚ) (c₀ : ℂ), IsCarriedPsi Ψ ∧ QuasiIso Ψ ∧ Ψ ≫ augB = augR ∧ κ ≠ 0 ∧
    c₀ ≠ 0 ∧ PairGeo Ψ Ω κ ∧ ∀ f : closedEdgeCochains rationalLevel, levelTrace f = c₀ * evalOmega (cornerChain Ω) f.1

/-- The cycle of `exists_pairGeo` has geometric data. -/
theorem exists_geoData : ∃ Ω : coneR.X 4, IsCoinvCycle Ω ∧ GeoData Ω := by
  obtain ⟨Ω, Ψ, κ, c₀, hcyc, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩ := exists_pairGeo
  exact ⟨Ω, hcyc, Ψ, κ, c₀, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩

/-- **Geometric Stokes for a cycle with geometric data** (`exists_stokes_cycle` for the given `Ω`). -/
theorem stokes_of_geoData {Ω : coneR.X 4} (hG : GeoData Ω) :
    ∀ {V : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ dualRepresentation V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0),
      conePair (evalRep V) Ω (coneToPt.f 2 ≫ f) (coneToPt.f 2 ≫ f') = 0 := by
  obtain ⟨Ψ, κ, c₀, hcar, hq, haug, hκ, hc₀, pairGeo, htr⟩ := hG
  intro V f hf f' hf'
  have hB : coneR.d 3 2 ≫ coneToPt.f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, hf, comp_zero]
  have hA : coneR.d 3 2 ≫ coneToPt.f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← coneToPt.comm 3 2, Category.assoc, hf', comp_zero]
  obtain ⟨β, hβ, hPB⟩ := exists_pullsBackTo hq _ hB
  obtain ⟨α, hα, hPA⟩ := exists_pullsBackTo hq _ hA
  have hpair := pairGeo _ _ β hβ α hα hA hPB hPA
  obtain ⟨η, hη⟩ := hPB
  obtain ⟨η', hη'⟩ := hPA
  have hβcls := cochainClass_eq_restrictedClass hq haug f hf β hβ η hη
  have hαcls := cochainClass_eq_restrictedClass hq haug f' hf' α hα η' hη'
  have hgeo : geoOf V α hα β hβ = 0 := by
    unfold geoOf
    rw [hβcls, hαcls]
    exact geoPairing_restrictedClass_zero V _ _
  have h0 : conePair (evalRep V) Ω (coneToPt.f 2 ≫ f) (coneToPt.f 2 ≫ f') = κ * geoOf V α hα β hβ := hpair
  rw [h0, hgeo, mul_zero]

/-- **Stokes in cone form, for the cycle with geometric data** (`cone_stokes` for the given `Ω`). -/
theorem cone_stokes_of_geoData {Ω : coneR.X 4} (hΩ : IsCoinvCycle Ω) (hG : GeoData Ω) :
    ∀ {V : Rep.{0} ℚ Γ6} (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ dualRepresentation V)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
      (w : A.X 1 ⟶ V) (_ : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
      (w' : A.X 1 ⟶ dualRepresentation V) (_ : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f'),
      conePair (evalRep V) Ω (lineCone w ((ptMap Line).f 2 ≫ f)) (lineCone w' ((ptMap Line).f 2 ≫ f')) +
        conePair (evalRep V) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
          (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 := by
  intro V f hf f' hf' w hw w' hw'
  have h0 := stokes_of_geoData hG f hf f' hf'
  rw [coneToPt_eq_lift f w, coneToPt_eq_lift f' w', conePair_add_left, conePair_add_right,
    conePair_add_right] at h0
  have hLP : conePair (evalRep V) Ω (lineCone w ((ptMap Line).f 2 ≫ f))
      (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 :=
    conePair_linePlane_zero _ _ _ _ (lineCone_plane _ _) (planeCone_line _ _) hΩ
  have hf1 : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ (ptMap Line).f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← (ptMap Line).comm 3 2, Category.assoc, hf, comp_zero]
  have hf2 : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ (ptMap Plane).f 2 ≫ f = 0 := by
    rw [← Category.assoc, ← (ptMap Plane).comm 3 2, Category.assoc, hf, comp_zero]
  have hf1' : (prodComplex Γ6 RationalGL3 Line).d 3 2 ≫ (ptMap Line).f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← (ptMap Line).comm 3 2, Category.assoc, hf', comp_zero]
  have hf2' : (prodComplex Γ6 RationalGL3 Plane).d 3 2 ≫ (ptMap Plane).f 2 ≫ f' = 0 := by
    rw [← Category.assoc, ← (ptMap Plane).comm 3 2, Category.assoc, hf', comp_zero]
  have hPL : conePair (evalRep V) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
      (lineCone w' ((ptMap Line).f 2 ≫ f')) = 0 :=
    cone_cross_zero _ _ _
      (planeCone_cocycle _ _ hf2 (plane_edge_of_line_edge f w hw))
      (lineCone_cocycle _ _ hf1' hw')
      (planeCone_line _ _) (lineCone_plane _ _) Ω hΩ
  rw [hLP, hPL] at h0
  simpa using h0

/-- **Lemma `ar:lem:stokes` at level `Γ(6)` in cone form, for a complex coefficient module and its literal complex dual, for a cycle with geometric data.** -/
theorem cone_stokes_complex_of_geoData {Ω : coneR.X 4} (hΩ : IsCoinvCycle Ω) (hG : GeoData Ω) :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
      {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)
      (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ.dual)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
      (w : A.X 1 ⟶ qRep ι ρ) (_ : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
      (w' : A.X 1 ⟶ qRep ι ρ.dual) (_ : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f'),
      conePairC (evalC ι ρ) Ω (lineCone w ((ptMap Line).f 2 ≫ f)) (lineCone w' ((ptMap Line).f 2 ≫ f')) +
        conePairC (evalC ι ρ) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
          (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 := by
  intro V _ _ _ _ G _ ι ρ f hf f' hf' w hw w' hw'
  apply eq_zero_of_forall_rat_functional
  intro r
  have h := cone_stokes_of_geoData hΩ hG (V := qRep ι ρ) f hf (f' ≫ dualEmb ι ρ r)
    (by rw [← Category.assoc, hf', zero_comp]) w hw
    (w' ≫ dualEmb ι ρ r) (by rw [← Category.assoc, hw']; simp only [Category.assoc])
  have e1 : lineCone (w' ≫ dualEmb ι ρ r) ((ptMap Line).f 2 ≫ f' ≫ dualEmb ι ρ r) =
      lineCone w' ((ptMap Line).f 2 ≫ f') ≫ dualEmb ι ρ r := by
    rw [lineCone_comp, Category.assoc]
  have e2 : planeCone (w' ≫ dualEmb ι ρ r) ((ptMap Plane).f 2 ≫ f' ≫ dualEmb ι ρ r) =
      planeCone w' ((ptMap Plane).f 2 ≫ f') ≫ dualEmb ι ρ r := by
    rw [planeCone_comp, Category.assoc]
  rw [e1, e2, conePair_dualEmb, conePair_dualEmb] at h
  rw [map_add]
  exact h

/-- **`cone_stokes_complex`, with the geometric data of the cycle retained.** -/
theorem cone_stokes_geo : ∃ Ω : coneR.X 4, IsCoinvCycle Ω ∧ GeoData Ω ∧
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [Module ℚ V] [IsScalarTower ℚ ℂ V]
      {G : Type} [Group G] (ι : Γ6 →* G) (ρ : Representation ℂ G V)
      (f : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f = 0)
      (f' : (prodComplex Γ6 RationalGL3 PUnit).X 2 ⟶ qRep ι ρ.dual)
      (_ : (prodComplex Γ6 RationalGL3 PUnit).d 3 2 ≫ f' = 0)
      (w : A.X 1 ⟶ qRep ι ρ) (_ : A.d 2 1 ≫ w = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f)
      (w' : A.X 1 ⟶ qRep ι ρ.dual) (_ : A.d 2 1 ≫ w' = flagLineHom.hom.f 2 ≫ (ptMap Line).f 2 ≫ f'),
      conePairC (evalC ι ρ) Ω (lineCone w ((ptMap Line).f 2 ≫ f)) (lineCone w' ((ptMap Line).f 2 ≫ f')) +
        conePairC (evalC ι ρ) Ω (planeCone w ((ptMap Plane).f 2 ≫ f))
          (planeCone w' ((ptMap Plane).f 2 ≫ f')) = 0 := by
  obtain ⟨Ω, hΩ, hG⟩ := exists_geoData
  exact ⟨Ω, hΩ, hG, cone_stokes_complex_of_geoData hΩ hG⟩

end TernaryPeriodPolynomials.Argument.GammaNStokes
