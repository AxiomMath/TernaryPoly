module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Support
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.Const.Rel

@[expose] public section


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

/-!
# Transport of the flag classes to the base line (M3a(i-b))

Formalized by Claude Sonnet 5.5.

* `faceCoord_conj_gen`: the Shapiro coordinate at `z = γ • R` of any cochain class is the conjugation transport of the coordinate at `R` (no pullback; the generic version of the `faceCoord_pullback_conj`);
* `flagConjTransport`, `lineFlagClass_conj`, `planeFlagClass_conj`: the flag class at the flag orbit `o` is the conjugation transport of the class at the base flag `F₀` (`o.out = g • F₀`);
* `baseFlag o = (lineConj o)⁻¹ • o.out` has the base line `(flagLineOrbit o).out` (`flagLine_baseFlag`); `lineFlagClass_baseline`: its class at the base flag is the explicit cup cocycle
  `w̄ ⌣ z̄' - γ̄` of `lineFlag_faceCoord` (bar cochains at the base flag/line);
* `lineFlag_sum_conj`, `planeFlag_sum_conj`: the sum identity of M3a(i): with the cut primitive, `∑_o lam o (class o)` is the sum over the flag orbits over the face of `lam o` of the transported class.
What remains for the identification with `lamQ_c [flagCup …]` is the compatibility of `E.lam o` with `flagConjTransport` (the frame independence of `G_F`, `FlagH3/FrameIndep`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

section Generic

variable {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z]

/-- **The Shapiro coordinate at `z = γ • R` is the transport of the coordinate at `R`** (any cochain class; no pullback). -/
theorem faceCoord_conj_gen (hfree : ∀ (γ : Γ) (v : V), γ • v = v → γ = 1)
    (S : Subgroup Γ) (W : Rep.{0} ℚ Γ) (v₀ : V) (z : Z) (hz : ∀ g : S, g • z = z)
    (γ : Γ) (R : Z) (hR : z = γ • R)
    (f : S →* MulAction.stabilizer Γ R) (hf : ∀ s : S, (f s : Γ) = γ⁻¹ * s * γ) (n : ℕ) :
    faceCoord S W v₀ z hz n =
      faceCoord (MulAction.stabilizer Γ R) W v₀ R (fun g => g.2) n ≫
        groupCohomology.map f (conjComparison W γ (MulAction.stabilizer Γ R) S f hf) n := by
  have hS2 : ∀ g : S, g • (γ • R) = γ • R := fun g => hR ▸ hz g
  rw [faceCoord_eq_homologyMap_stabCoord S W v₀ z hz n,
    faceCoord_eq_homologyMap_stabCoord (MulAction.stabilizer Γ R) W v₀ R (fun g => g.2) n,
    stabCoord_congr_pt S W v₀ hR hz hS2,
    homologyMap_stabCoord_conj W v₀ R γ (MulAction.stabilizer Γ R) S (fun g => g.2) hS2 f hf hfree n,
    Category.assoc, Category.assoc]
  congr 1
  exact barChainMap_homology f (conjComparison W γ (MulAction.stabilizer Γ R) S f hf) n

end Generic

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

section Flags

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- The transport `H³(Stab F₀) → H³(Stab (g • F₀))` along conjugation `s ↦ g⁻¹ s g`. -/
def flagConjTransport (g : Γ6) (F₀ : Flag) (o : labelOrbits Γ6 Flag) (hF₀ : o.out = g • F₀) :
    groupCohomology (Rep.res (MulAction.stabilizer Γ6 F₀).subtype Wq) 3 ⟶
      groupCohomology (Rep.res (MulAction.stabilizer Γ6 o.out).subtype Wq) 3 :=
  groupCohomology.map (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
    (conjComparison Wq g (MulAction.stabilizer Γ6 F₀) (MulAction.stabilizer Γ6 o.out)
      (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
      (conjStabHom_apply g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))) 3

/-- **The flag class at the flag orbit `o` is the conjugation transport of the class at the base flag `F₀` with `o.out = g • F₀`** (lines).  Combined with `lineFlag_faceCoord` at `F₀`
(bar cochains of `d.w` at `F₀` and of `e.z`, `γ` at the line `flagLine F₀`) this is the explicit cup-cocycle form of the class at the base flag. -/
theorem lineFlagClass_conj (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (o : labelOrbits Γ6 Flag) (g : Γ6) (F₀ : Flag) (hF₀ : o.out = g • F₀) :
    lineFlagClass π d e γ hγ o = (flagConjTransport g F₀ o hF₀).hom
      ((faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
        (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (lineFlagCochain π d.w e.z γ)
          (lineFlagCochain_cocycle π d e γ hγ))) :=
  congrArg (fun φ => φ.hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
      (lineFlagCochain π d.w e.z γ) (lineFlagCochain_cocycle π d e γ hγ)))
    (faceCoord_conj_gen vertexAction_free' (MulAction.stabilizer Γ6 o.out) Wq (1 : RationalGL3) o.out (fun g => g.2) g F₀ hF₀
      (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
      (conjStabHom_apply g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2)) 3)

/-- … for planes. -/
theorem planeFlagClass_conj (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (o : labelOrbits Γ6 Flag) (g : Γ6) (F₀ : Flag) (hF₀ : o.out = g • F₀) :
    planeFlagClass π d e γ hγ o = (flagConjTransport g F₀ o hF₀).hom
      ((faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
        (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (planeFlagCochain π d.z e.w γ)
          (planeFlagCochain_cocycle π d e γ hγ))) :=
  congrArg (fun φ => φ.hom (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
      (planeFlagCochain π d.z e.w γ) (planeFlagCochain_cocycle π d e γ hγ)))
    (faceCoord_conj_gen vertexAction_free' (MulAction.stabilizer Γ6 o.out) Wq (1 : RationalGL3) o.out (fun g => g.2) g F₀ hF₀
      (conjStabHom g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2))
      (conjStabHom_apply g F₀ (MulAction.stabilizer Γ6 o.out) (fun s => by rw [← hF₀]; exact s.2)) 3)

/-- The base flag of a flag orbit: `g⁻¹ • o.out`, `g = lineConj o`; its line is the representative of the line orbit of `o`. -/
def baseFlag (o : labelOrbits Γ6 Flag) : Flag := (lineConj o)⁻¹ • o.out

theorem out_eq_conj_baseFlag (o : labelOrbits Γ6 Flag) : o.out = lineConj o • baseFlag o :=
  (smul_inv_smul (lineConj o) o.out).symm

theorem flagLine_baseFlag (o : labelOrbits Γ6 Flag) : flagLineOf (baseFlag o) = (flagLineOrbit o).out := by
  have h := lineConj_smul o
  have e : flagLineOf ((lineConj o)⁻¹ • o.out) = (lineConj o)⁻¹ • flagLineOf o.out :=
    TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant _ _
  change flagLineOf ((lineConj o)⁻¹ • o.out) = _
  rw [e, ← h, inv_smul_smul]

/-- **M3a(i-b), lines, explicit form.**  The flag class at `o` is the conjugation transport, from the stabilizer of the base flag `baseFlag o` (whose line is the base line
`(flagLineOrbit o).out`), of the class of the explicit cup cocycle `w̄ ⌣ z̄' - γ̄` (bar cochains of `d.w` at the base flag, of `e.z` and `γ` at the base line). -/
theorem lineFlagClass_baseline (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (o : labelOrbits Γ6 Flag) :
    ∃ hd : inhomogeneousCochains.d (Rep.res (MulAction.stabilizer Γ6 (baseFlag o)).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3
        (fun x : Fin 3 → MulAction.stabilizer Γ6 (baseFlag o) =>
          cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 (baseFlag o)).subtype) (pairOf π)
            (fun s : MulAction.stabilizer Γ6 (baseFlag o) =>
              barCochain (MulAction.stabilizer Γ6 (baseFlag o)) (1 : RationalGL3) (baseFlag o) d.w (fun _ : Fin 1 => s))
            (fun s t : MulAction.stabilizer Γ6 (baseFlag o) =>
              barCochain (MulAction.stabilizer Γ6 (baseFlag o)) (1 : RationalGL3) (flagLineOf (baseFlag o)) e.z
                (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
          barCochain (MulAction.stabilizer Γ6 (baseFlag o)) (1 : RationalGL3) (flagLineOf (baseFlag o)) γ x) = 0,
      lineFlagClass π d e γ hγ o = (flagConjTransport (lineConj o) (baseFlag o) o (out_eq_conj_baseFlag o)).hom
        ((groupCohomology.π (Rep.res (MulAction.stabilizer Γ6 (baseFlag o)).subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom
          (groupCohomology.cocyclesMk _ hd)) := by
  obtain ⟨hd, hcoh⟩ := lineFlag_faceCoord π (baseFlag o) (fun g => g.2) d.w e.z γ (lineFlagCochain_cocycle π d e γ hγ)
  exact ⟨hd, (lineFlagClass_conj π d e γ hγ o (lineConj o) (baseFlag o) (out_eq_conj_baseFlag o)).trans
    (congrArg _ hcoh)⟩

open Classical in
/-- **M3a(i), lines: the sum identity.**  For the cut primitive `γ' = cut_S ∘ γ` (data supported on the orbit `S`), the sum over all flag orbits of `E.lam o` of the flag classes is the sum
over the flag orbits over `S` of `E.lam o` of the conjugation transport of the class at the base flag `baseFlag o`. -/
theorem lineFlag_sum_conj (E : FlagEval) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    ∑ o, E.lam o (lineFlagClass π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (cutγ_line_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagLineOf o.out ∈ S),
        E.lam o ((flagConjTransport (lineConj o) (baseFlag o) o (out_eq_conj_baseFlag o)).hom
          ((faceCoord (MulAction.stabilizer Γ6 (baseFlag o)) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) (baseFlag o)
            (fun g => g.2) 3).hom
            (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
              (lineFlagCochain π d.w e.z (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ))
              (lineFlagCochain_cocycle π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he))))) := by
  refine (lineFlag_sum_eq_filter π E d e γ hγ S hS hd he).trans (Finset.sum_congr rfl fun o _ => ?_)
  rw [lineFlagClass_conj π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he) o (lineConj o) (baseFlag o)
    (out_eq_conj_baseFlag o)]

open Classical in
/-- … planes. -/
theorem planeFlag_sum_conj (E : FlagEval) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (hd : d.IsOn S) (he : e.IsOn S) :
    ∑ o, E.lam o (planeFlagClass π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (cutγ_plane_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagPlaneOf o.out ∈ S),
        E.lam o ((flagConjTransport (planeConj o) ((planeConj o)⁻¹ • o.out) o (smul_inv_smul (planeConj o) o.out).symm).hom
          ((faceCoord (MulAction.stabilizer Γ6 ((planeConj o)⁻¹ • o.out)) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3)
            ((planeConj o)⁻¹ • o.out) (fun g => g.2) 3).hom
            (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6)))
              (planeFlagCochain π d.z e.w (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ))
              (planeFlagCochain_cocycle π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he))))) := by
  refine (planeFlag_sum_eq_filter π E d e γ hγ S hS hd he).trans (Finset.sum_congr rfl fun o _ => ?_)
  rw [planeFlagClass_conj π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he) o (planeConj o) ((planeConj o)⁻¹ • o.out)
    (smul_inv_smul (planeConj o) o.out).symm]

end Flags

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
