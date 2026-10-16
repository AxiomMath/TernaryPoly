module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.Conj
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Bridge
public import TernaryPeriodPolynomials.ArithmeticCohomology.FlagH3.Sum7
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.Stokes.BClass

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
# The Q-level reduction of the flag sum (M3a): `∑_o λ_o(flag class) = ∑_{o over the face} (Σ7(w̄ ⌣ z̄') - Σ7(γ̄))` in the base flag groups

Formalized by Claude Sonnet 5.5.

* `res_cocyclesMk_eq_clsRes`, `flagLam_clsRes`: the class of a rational 3-cocycle in the `Rep.res` form and `flagLam` of it (the datum on the trivial representation);
* `lineC1`, `lineC2` (`planeC1`, `planeC2`): the cochains `w̄ ⌣ z̄'`, `γ̄` (`z̄ ⌣ (-w̄')`, `γ̄`) of the flag cocycle at a flag `F₀`, as functions of three elements of `Stab F₀`;
* `flagLam_lineFlag`, `flagLam_planeFlag`: `λ_{F₀}` of the class at `F₀` is `Σ7 c₁ - Σ7 c₂` (resp. `Σ7 c₁ + Σ7 c₂`) for any frame `(X, Y)` with `D.z = heisCycle X Y` (the `lam_eval_sub`);
* `FlagEval.lam_eq_flagLam`: for the evaluation data `flagH3Data`, `E.lam o = flagLam o.out`;
* **`lineSum_reduction`, `planeSum_reduction`**: with the transport compatibility `flagLam o.out ∘ flagConjTransport = flagLam (baseFlag o)` as an explicit hypothesis (the `lam_conj_transport`) and frames
  `(X o, Y o)` of the base flag groups as parameters, the sum over all flag orbits of `E.lam o` of the flag classes for the cut primitive is the stated sum of `Σ7` terms over the flag orbits over the face;
* `barCochain_restrict`: bar cochains restrict along inclusions of subgroups (the `Stab F₀ ≤ Stab (base line)` bookkeeping).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

open TernaryPeriodPolynomials.Argument.FlagH3

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- The class of a rational `3`-cocycle of a subgroup `S ≤ Γ(6)` in the `Rep.res` form is `clsRes`. -/
theorem res_cocyclesMk_eq_clsRes (S : Subgroup Γ6) (θ : (Fin 3 → S) → ℚ)
    (hθ : inhomogeneousCochains.d (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3 θ = 0) (hθ' : dThree θ = 0) :
    (groupCohomology.π (Rep.res S.subtype (𝟙_ (Rep.{0} ℚ Γ6))) 3).hom (groupCohomology.cocyclesMk θ hθ) =
      clsRes S θ hθ' := by
  rw [clsRes_eq S θ hθ']
  have c1 : ∀ (G : Type) [Group G] (T : (Fin 3 → G) → ℚ) (h : dThree T = 0),
      cocycleClass T h = (groupCohomology.π (Rep.trivial ℚ G ℚ) 3).hom (groupCohomology.cocyclesMk T h) := fun _ _ _ _ => rfl
  rw [c1, map_cocycleClass (Rep.trivial ℚ S ℚ) _ (MonoidHom.id S) (trivToRes S) θ hθ']
  rfl

theorem flagLam_clsRes (F : Flag) (θ : (Fin 3 → MulAction.stabilizer Γ6 F) → ℚ) (hθ : dThree θ = 0) :
    flagLam F (clsRes (MulAction.stabilizer Γ6 F) θ hθ) = (flagStabDataOf F).lam (cocycleClass θ hθ) := by
  unfold flagLam clsRes
  simp



/-- The `cup12` term `w̄ ⌣ z̄'` of the flag cocycle at the flag `F₀`, as a function of three elements of the flag group `Stab F₀`. -/
def lineC1 (d : LineDatum W) (e : LineDatum W') (F₀ : Flag) :
    MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → ℚ :=
  cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
    (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ d.w (fun _ : Fin 1 => s))
    (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
      (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) e.z (fun j : Fin 2 => if j = 0 then s else t))

/-- The primitive term `γ̄` of the flag cocycle at the flag `F₀`. -/
def lineC2 (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → ℚ :=
  fun a b c => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
    (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) γ ![a, b, c]

/-- **`λ_{F₀}` of the class at the flag `F₀` of the corner cocycle is `Σ7 (w̄ ⌣ z̄') - Σ7 γ̄`**, for any frame `(X, Y)` of the flag group with `z = heisCycle X Y`. -/
theorem flagLam_lineFlag (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (F₀ : Flag) (X Y : MulAction.stabilizer Γ6 F₀) (hz : (flagStabDataOf F₀).z = heisCycle X Y) :
    flagLam F₀ ((faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
      (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (lineFlagCochain π d.w e.z γ)
        (lineFlagCochain_cocycle π d e γ hγ))) = sum7 X Y (lineC1 π d e F₀) - sum7 X Y (lineC2 γ F₀) := by
  obtain ⟨hd, hcoh⟩ := lineFlag_faceCoord π F₀ (fun g => g.2) d.w e.z γ (lineFlagCochain_cocycle π d e γ hγ)
  rw [hcoh]
  have hfun : (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ d.w (fun _ : Fin 1 => s))
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) e.z (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) γ x) =
      (fun g : Fin 3 → MulAction.stabilizer Γ6 F₀ => lineC1 π d e F₀ (g 0) (g 1) (g 2) - lineC2 γ F₀ (g 0) (g 1) (g 2)) := by
    funext x
    have hx : x = ![x 0, x 1, x 2] := by
      funext i; fin_cases i <;> rfl
    simp only [lineC1, lineC2]
    rw [← hx]
  have hθ : dThree (fun g : Fin 3 → MulAction.stabilizer Γ6 F₀ => lineC1 π d e F₀ (g 0) (g 1) (g 2) - lineC2 γ F₀ (g 0) (g 1) (g 2)) = 0 := by
    rw [← hfun]
    exact hd
  have hc : ∀ g1 g2 g3 g4, dd3T (fun a b c => lineC1 π d e F₀ a b c - lineC2 γ F₀ a b c) g1 g2 g3 g4 = 0 := by
    intro g1 g2 g3 g4
    have := congrFun hθ ![g1, g2, g3, g4]
    rw [dThree_eq_dd3T (fun a b c => lineC1 π d e F₀ a b c - lineC2 γ F₀ a b c)] at this
    exact this
  have hd' : dThree (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ d.w (fun _ : Fin 1 => s))
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) e.z (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) γ x) = 0 := hd
  rw [res_cocyclesMk_eq_clsRes _ _ hd hd', flagLam_clsRes]
  have hcc : ∀ (θ θ' : (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ) (h : θ = θ') (h1 : dThree θ = 0) (h2 : dThree θ' = 0),
      cocycleClass θ h1 = cocycleClass θ' h2 := by
    intro θ θ' h h1 h2; subst h; rfl
  rw [hcc _ _ hfun hd' hθ]
  exact (flagStabDataOf F₀).lam_eval_sub X Y hz _ _ hc



theorem sum7_neg {B : Type} [Group B] (X Y : B) (c : B → B → B → ℚ) : sum7 X Y (fun a b d => - c a b d) = - sum7 X Y c := by
  unfold sum7; ring

/-- The `cup21` term `z̄ ⌣ (-w̄')` of the plane flag cocycle at the flag `F₀`. -/
def planeC1 (d : PlaneDatum W) (e : PlaneDatum W') (F₀ : Flag) :
    MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → ℚ :=
  cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
    (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
      (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) d.z (fun j : Fin 2 => if j = 0 then s else t))
    (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ (-e.w) (fun _ : Fin 1 => s))

/-- The primitive term `γ̄` of the plane flag cocycle at the flag `F₀`. -/
def planeC2 (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → MulAction.stabilizer Γ6 F₀ → ℚ :=
  fun a b c => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
    (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) γ ![a, b, c]

/-- **`λ_{F₀}` of the class at the flag `F₀` of the plane corner cocycle is `Σ7 (z̄ ⌣ (-w̄')) + Σ7 γ̄`.** -/
theorem flagLam_planeFlag (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (F₀ : Flag) (X Y : MulAction.stabilizer Γ6 F₀) (hz : (flagStabDataOf F₀).z = heisCycle X Y) :
    flagLam F₀ ((faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
      (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (planeFlagCochain π d.z e.w γ)
        (planeFlagCochain_cocycle π d e γ hγ))) = sum7 X Y (planeC1 π d e F₀) + sum7 X Y (planeC2 γ F₀) := by
  obtain ⟨hd, hcoh⟩ := planeFlag_faceCoord π F₀ (fun g => g.2) d.z e.w γ (planeFlagCochain_cocycle π d e γ hγ)
  rw [hcoh]
  have hfun : (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) d.z (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ (-e.w) (fun _ : Fin 1 => s))
        (x 0) (x 1) (x 2) +
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) γ x) =
      (fun g : Fin 3 → MulAction.stabilizer Γ6 F₀ => planeC1 π d e F₀ (g 0) (g 1) (g 2) - (- planeC2 γ F₀ (g 0) (g 1) (g 2))) := by
    funext x
    have hx : x = ![x 0, x 1, x 2] := by
      funext i; fin_cases i <;> rfl
    simp only [planeC1, planeC2, sub_neg_eq_add]
    rw [← hx]
  have hθ : dThree (fun g : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      planeC1 π d e F₀ (g 0) (g 1) (g 2) - (- planeC2 γ F₀ (g 0) (g 1) (g 2))) = 0 := by
    rw [← hfun]
    exact hd
  have hc : ∀ g1 g2 g3 g4, dd3T (fun a b c => planeC1 π d e F₀ a b c - (fun a b c => - planeC2 γ F₀ a b c) a b c) g1 g2 g3 g4 = 0 := by
    intro g1 g2 g3 g4
    have := congrFun hθ ![g1, g2, g3, g4]
    rw [dThree_eq_dd3T (fun a b c => planeC1 π d e F₀ a b c - (fun a b c => - planeC2 γ F₀ a b c) a b c)] at this
    exact this
  have hd' : dThree (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) d.z (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ (-e.w) (fun _ : Fin 1 => s))
        (x 0) (x 1) (x 2) +
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) γ x) = 0 := hd
  rw [res_cocyclesMk_eq_clsRes _ _ hd hd', flagLam_clsRes]
  have hcc : ∀ (θ θ' : (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ) (h : θ = θ') (h1 : dThree θ = 0) (h2 : dThree θ' = 0),
      cocycleClass θ h1 = cocycleClass θ' h2 := by
    intro θ θ' h h1 h2; subst h; rfl
  rw [hcc _ _ hfun hd' hθ]
  have := (flagStabDataOf F₀).lam_eval_sub X Y hz _ _ hc
  rw [this, sum7_neg]
  ring



/-- If the evaluation data is S3's `flagH3Data`, then `E.lam o = flagLam o.out`. -/
theorem FlagEval.lam_eq_flagLam (E : FlagEval) (hE : E.D = flagH3Data) (o : labelOrbits Γ6 Flag) :
    E.lam o = flagLam o.out := by
  have hG : E.D.G o = flagGen o.out := by rw [hE]; rfl
  have h1 : E.lam o (flagGen o.out) = 1 := by rw [← hG]; exact E.lam_G o
  apply LinearMap.ext
  intro x
  conv_lhs => rw [flagLam_eq_smul_flagGen o.out x]
  rw [map_smul, h1, smul_eq_mul, mul_one]

open Classical in
/-- **M3a reduction, lines.**  Data `d`, `e` supported on the orbit `S` of the base line, `γ' = cut_S ∘ γ` the cut primitive.  Assume (a) the evaluation data is `flagH3Data` (`λ_o = flagLam o.out`),
(b) the transport compatibility `flagLam o.out ∘ flagConjTransport = flagLam (baseFlag o)` (S3's `lam_conj_transport`), and (c) frames `(X o, Y o)` of the flag group of the base flag with
`D.z = heisCycle (X o) (Y o)`.  Then the sum over all flag orbits of `E.lam o` of the flag classes is the sum over the flag orbits over `S` of `Σ7(w̄_o ⌣ z̄'|) - Σ7(γ̄|)` in the base flag groups. -/
theorem lineSum_reduction (E : FlagEval) (hE : E.D = flagH3Data) (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (hd : d.IsOn S) (he : e.IsOn S)
    (hconj : ∀ (o : labelOrbits Γ6 Flag) (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 (baseFlag o)).subtype Wq) 3),
      flagLam o.out ((flagConjTransport (lineConj o) (baseFlag o) o (out_eq_conj_baseFlag o)).hom x) = flagLam (baseFlag o) x)
    (X Y : ∀ o : labelOrbits Γ6 Flag, MulAction.stabilizer Γ6 (baseFlag o))
    (hz : ∀ o, (flagStabDataOf (baseFlag o)).z = heisCycle (X o) (Y o)) :
    ∑ o, E.lam o (lineFlagClass π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (cutγ_line_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagLineOf o.out ∈ S),
        (sum7 (X o) (Y o) (lineC1 π d e (baseFlag o)) - sum7 (X o) (Y o) (lineC2 (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (baseFlag o))) := by
  rw [lineFlag_sum_conj π E d e γ hγ S hS hd he]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [FlagEval.lam_eq_flagLam E hE o, hconj o, flagLam_lineFlag π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he)
    (baseFlag o) (X o) (Y o) (hz o)]

open Classical in
/-- **M3a reduction, planes.** -/
theorem planeSum_reduction (E : FlagEval) (hE : E.D = flagH3Data) (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (hd : d.IsOn S) (he : e.IsOn S)
    (hconj : ∀ (o : labelOrbits Γ6 Flag) (x : groupCohomology (Rep.res (MulAction.stabilizer Γ6 ((planeConj o)⁻¹ • o.out)).subtype Wq) 3),
      flagLam o.out ((flagConjTransport (planeConj o) ((planeConj o)⁻¹ • o.out) o (smul_inv_smul (planeConj o) o.out).symm).hom x) =
        flagLam ((planeConj o)⁻¹ • o.out) x)
    (X Y : ∀ o : labelOrbits Γ6 Flag, MulAction.stabilizer Γ6 ((planeConj o)⁻¹ • o.out))
    (hz : ∀ o, (flagStabDataOf ((planeConj o)⁻¹ • o.out)).z = heisCycle (X o) (Y o)) :
    ∑ o, E.lam o (planeFlagClass π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (cutγ_plane_primitive π d e γ hγ S hS hd he) o) =
      ∑ o ∈ Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagPlaneOf o.out ∈ S),
        (sum7 (X o) (Y o) (planeC1 π d e ((planeConj o)⁻¹ • o.out)) +
          sum7 (X o) (Y o) (planeC2 (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) ((planeConj o)⁻¹ • o.out))) := by
  rw [planeFlag_sum_conj π E d e γ hγ S hS hd he]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [FlagEval.lam_eq_flagLam E hE o, hconj o, flagLam_planeFlag π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he)
    ((planeConj o)⁻¹ • o.out) (X o) (Y o) (hz o)]



/-- Bar cochains restrict along inclusions of subgroups: the Q-level bar cochain restricted to `B ≤ Q` is the `B`-level one. -/
theorem barCochain_restrict {Γ : Type} [Group Γ] {V Z : Type} [MulAction Γ V] [MulAction Γ Z] {W : Rep.{0} ℚ Γ} {k : ℕ}
    (T₁ T₂ : Subgroup Γ) (h : T₁ ≤ T₂) (v₀ : V) (z : Z) (f : (prodComplex Γ V Z).X k ⟶ W) (x : Fin k → T₁) :
    barCochain T₁ v₀ z f x = barCochain T₂ v₀ z f (fun i => Subgroup.inclusion h (x i)) := by
  unfold barCochain barSimplex
  congr 3
  funext i
  have : ((Fin.partialProd (fun j => Subgroup.inclusion h (x j)) i : T₂) : Γ) = ((Fin.partialProd x i : T₁) : Γ) := by
    induction i using Fin.induction with
    | zero => simp [Fin.partialProd_zero]
    | succ j ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, Subgroup.coe_mul, Subgroup.coe_mul, ih]; rfl
  rw [this]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
