module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.SumReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.Flag.EvalInst

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
# M3a reduction for an arbitrary system of base flags (no frames, no `Σ7`)

Formalized by Claude Sonnet 5.5.

`lineTheta`/`planeTheta`: the explicit rational 3-cochain (cup12 `w̄ ⌣ z̄'` minus `γ̄`; resp. cup21 `z̄ ⌣ (-w̄')` plus `γ̄`) of the flag group `Stab F₀`; `lineTheta_dThree`/`planeTheta_dThree` (cocycle),
`lineFlag_coord_eq_clsRes`/`planeFlag_coord_eq_clsRes` (the Shapiro coordinate at `F₀` is its class `clsRes`).  **`lineSum_general`/`planeSum_general`**: if `Fc : I → Flag` are flags over a line (plane) `b ∈ S`
representing bijectively the flag orbits over `S`, then for `E = flagEval` and the cut primitive, `∑_o E.lam o (flag class o) = ∑_c flagLam (Fc c) (clsRes (Stab Fc) Θ_c)`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

attribute [local instance] TernaryPeriodPolynomials.Argument.FacePairingFull.Comparison.vertexAction

open TernaryPeriodPolynomials.Argument.FlagH3

variable {W W' : Rep.{0} ℚ Γ6} (π : W ⊗ W' ⟶ 𝟙_ (Rep.{0} ℚ Γ6))

/-- The explicit rational 3-cochain `w̄ ⌣ z̄' - γ̄` of the line flag cocycle at the flag `F₀`. -/
def lineTheta (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ :=
  fun g => lineC1 π d e F₀ (g 0) (g 1) (g 2) - lineC2 γ F₀ (g 0) (g 1) (g 2)

/-- The explicit rational 3-cochain `z̄ ⌣ (-w̄') + γ̄` of the plane flag cocycle at the flag `F₀`. -/
def planeTheta (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ :=
  fun g => planeC1 π d e F₀ (g 0) (g 1) (g 2) - (- planeC2 γ F₀ (g 0) (g 1) (g 2))



theorem lineTheta_hfun (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup12 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ d.w (fun _ : Fin 1 => s))
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) e.z (fun j : Fin 2 => if j = 0 then s else t)) (x 0) (x 1) (x 2) -
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagLine F₀) γ x) =
      lineTheta π d e γ F₀ := by
  funext x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i; fin_cases i <;> rfl
  simp only [lineTheta, lineC1, lineC2]
  rw [← hx]

theorem lineTheta_dThree (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (F₀ : Flag) :
    dThree (lineTheta π d e γ F₀) = 0 := by
  obtain ⟨hd, -⟩ := lineFlag_faceCoord π F₀ (fun g => g.2) d.w e.z γ (lineFlagCochain_cocycle π d e γ hγ)
  rw [← lineTheta_hfun π d e γ F₀]
  exact hd

/-- **The coordinate at the flag `F₀` of the line corner cocycle is the class `clsRes` of the explicit cocycle `lineTheta`.** -/
theorem lineFlag_coord_eq_clsRes (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (F₀ : Flag) :
    (faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
      (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (lineFlagCochain π d.w e.z γ)
        (lineFlagCochain_cocycle π d e γ hγ)) =
      clsRes (MulAction.stabilizer Γ6 F₀) (lineTheta π d e γ F₀) (lineTheta_dThree π d e γ hγ F₀) := by
  obtain ⟨hd, hcoh⟩ := lineFlag_faceCoord π F₀ (fun g => g.2) d.w e.z γ (lineFlagCochain_cocycle π d e γ hγ)
  rw [hcoh, res_cocyclesMk_eq_clsRes _ _ hd (by exact hd)]
  have hcc : ∀ (θ θ' : (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ) (h : θ = θ') (h1 : dThree θ = 0) (h2 : dThree θ' = 0),
      clsRes (MulAction.stabilizer Γ6 F₀) θ h1 = clsRes (MulAction.stabilizer Γ6 F₀) θ' h2 := by
    intro θ θ' h h1 h2; subst h; rfl
  exact hcc _ _ (lineTheta_hfun π d e γ F₀) _ _



open Classical in
/-- **M3a reduction for an arbitrary system of base flags over a line `b` of the orbit `S` (lines).**  If `Fc : I → Flag` are flags over `b` representing, bijectively, the flag orbits over `S`, then for
`E = flagEval` and the cut primitive, `∑_o λ_o(flag class) = ∑_c λ_{F_c}[w̄ ⌣ z̄' - γ̄]`, the cocycles `lineTheta` of the flag groups `Stab F_c`. -/
theorem lineSum_general (d : LineDatum W) (e : LineDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Line).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Line).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Line).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Line) (hS : ∀ (γ : Γ6) (ℓ : Line), γ • ℓ ∈ S ↔ ℓ ∈ S) (hd : d.IsOn S) (he : e.IsOn S)
    (b : Line) (hb : b ∈ S) {I : Type} [Fintype I] (Fc : I → Flag) (hFc : ∀ c, flagLineOf (Fc c) = b)
    (hinj : Function.Injective (fun c => (Quotient.mk'' (Fc c) : labelOrbits Γ6 Flag)))
    (hsurj : ∀ o : labelOrbits Γ6 Flag, flagLineOf o.out ∈ S → ∃ c, (Quotient.mk'' (Fc c) : labelOrbits Γ6 Flag) = o) :
    ∑ o, flagEval.lam o (lineFlagClass π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (cutγ_line_primitive π d e γ hγ S hS hd he) o) =
      ∑ c : I, flagLam (Fc c) (clsRes (MulAction.stabilizer Γ6 (Fc c)) (lineTheta π d e (cutHom Γ6 RationalGL3 Line S hS 3 ≫ γ) (Fc c))
        (lineTheta_dThree π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he) (Fc c))) := by
  rw [lineFlag_sum_eq_filter π flagEval d e γ hγ S hS hd he]
  let φ : I → labelOrbits Γ6 Flag := fun c => Quotient.mk'' (Fc c)
  have himg : Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagLineOf o.out ∈ S) = Finset.univ.image φ := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ho
      obtain ⟨c, hc⟩ := hsurj o ho
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨g, hg⟩ := exists_conj_of_orbit (Fc c) (φ c) rfl
      have h1 : flagLineOf (φ c).out = g⁻¹ • b := by
        have : (φ c).out = g⁻¹ • Fc c := by rw [← hg, inv_smul_smul]
        rw [this, ← hFc c]
        exact TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagLine_equivariant _ _
      rw [h1]
      exact (hS g⁻¹ b).2 hb
  rw [himg, Finset.sum_image (fun x _ y _ h => hinj h)]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := exists_conj_of_orbit (Fc c) (φ c) rfl
  have hF : (φ c).out = g⁻¹ • Fc c := by rw [← hg, inv_smul_smul]
  rw [lineFlagClass_conj π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he) (φ c) g⁻¹ (Fc c) hF, flagEval_lam_conj g⁻¹ (Fc c) (φ c) hF,
    lineFlag_coord_eq_clsRes π d e _ (cutγ_line_primitive π d e γ hγ S hS hd he) (Fc c)]



theorem planeTheta_hfun (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6)) (F₀ : Flag) :
    (fun x : Fin 3 → MulAction.stabilizer Γ6 F₀ =>
      cup21 ((W'.ρ).comp (MulAction.stabilizer Γ6 F₀).subtype) (pairOf π)
        (fun s t : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3)
          (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) d.z (fun j : Fin 2 => if j = 0 then s else t))
        (fun s : MulAction.stabilizer Γ6 F₀ => barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) F₀ (-e.w) (fun _ : Fin 1 => s))
        (x 0) (x 1) (x 2) +
      barCochain (MulAction.stabilizer Γ6 F₀) (1 : RationalGL3) (SymmetricSpaceBoundaryFaceAugmentation.flagPlane F₀) γ x) =
      planeTheta π d e γ F₀ := by
  funext x
  have hx : x = ![x 0, x 1, x 2] := by
    funext i; fin_cases i <;> rfl
  simp only [planeTheta, planeC1, planeC2, sub_neg_eq_add]
  rw [← hx]

theorem planeTheta_dThree (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (F₀ : Flag) :
    dThree (planeTheta π d e γ F₀) = 0 := by
  obtain ⟨hd, -⟩ := planeFlag_faceCoord π F₀ (fun g => g.2) d.z e.w γ (planeFlagCochain_cocycle π d e γ hγ)
  rw [← planeTheta_hfun π d e γ F₀]
  exact hd

/-- **The coordinate at the flag `F₀` of the plane corner cocycle is the class `clsRes` of `planeTheta`.** -/
theorem planeFlag_coord_eq_clsRes (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π) (F₀ : Flag) :
    (faceCoord (MulAction.stabilizer Γ6 F₀) (𝟙_ (Rep.{0} ℚ Γ6)) (1 : RationalGL3) F₀ (fun g => g.2) 3).hom
      (clsS (homCochains (prodComplex Γ6 RationalGL3 Flag) (𝟙_ (Rep.{0} ℚ Γ6))) (planeFlagCochain π d.z e.w γ)
        (planeFlagCochain_cocycle π d e γ hγ)) =
      clsRes (MulAction.stabilizer Γ6 F₀) (planeTheta π d e γ F₀) (planeTheta_dThree π d e γ hγ F₀) := by
  obtain ⟨hd, hcoh⟩ := planeFlag_faceCoord π F₀ (fun g => g.2) d.z e.w γ (planeFlagCochain_cocycle π d e γ hγ)
  rw [hcoh, res_cocyclesMk_eq_clsRes _ _ hd (by exact hd)]
  have hcc : ∀ (θ θ' : (Fin 3 → MulAction.stabilizer Γ6 F₀) → ℚ) (h : θ = θ') (h1 : dThree θ = 0) (h2 : dThree θ' = 0),
      clsRes (MulAction.stabilizer Γ6 F₀) θ h1 = clsRes (MulAction.stabilizer Γ6 F₀) θ' h2 := by
    intro θ θ' h h1 h2; subst h; rfl
  exact hcc _ _ (planeTheta_hfun π d e γ F₀) _ _

open Classical in
/-- **M3a reduction for an arbitrary system of base flags over a plane `b` of the orbit `S` (planes).** -/
theorem planeSum_general (d : PlaneDatum W) (e : PlaneDatum W')
    (γ : (prodComplex Γ6 RationalGL3 Plane).X 3 ⟶ 𝟙_ (Rep.{0} ℚ Γ6))
    (hγ : (prodComplex Γ6 RationalGL3 Plane).d 4 3 ≫ γ =
      (nerveDiagSystem Γ6 RationalGL3 Plane).Δ 2 2 4 rfl ≫ (d.z ⊗ₘ e.z) ≫ π)
    (S : Set Plane) (hS : ∀ (γ : Γ6) (P : Plane), γ • P ∈ S ↔ P ∈ S) (hd : d.IsOn S) (he : e.IsOn S)
    (b : Plane) (hb : b ∈ S) {I : Type} [Fintype I] (Pc : I → Flag) (hPc : ∀ c, flagPlaneOf (Pc c) = b)
    (hinj : Function.Injective (fun c => (Quotient.mk'' (Pc c) : labelOrbits Γ6 Flag)))
    (hsurj : ∀ o : labelOrbits Γ6 Flag, flagPlaneOf o.out ∈ S → ∃ c, (Quotient.mk'' (Pc c) : labelOrbits Γ6 Flag) = o) :
    ∑ o, flagEval.lam o (planeFlagClass π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (cutγ_plane_primitive π d e γ hγ S hS hd he) o) =
      ∑ c : I, flagLam (Pc c) (clsRes (MulAction.stabilizer Γ6 (Pc c)) (planeTheta π d e (cutHom Γ6 RationalGL3 Plane S hS 3 ≫ γ) (Pc c))
        (planeTheta_dThree π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he) (Pc c))) := by
  rw [planeFlag_sum_eq_filter π flagEval d e γ hγ S hS hd he]
  let φ : I → labelOrbits Γ6 Flag := fun c => Quotient.mk'' (Pc c)
  have himg : Finset.univ.filter (fun o : labelOrbits Γ6 Flag => flagPlaneOf o.out ∈ S) = Finset.univ.image φ := by
    ext o
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro ho
      obtain ⟨c, hc⟩ := hsurj o ho
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      obtain ⟨g, hg⟩ := exists_conj_of_orbit (Pc c) (φ c) rfl
      have h1 : flagPlaneOf (φ c).out = g⁻¹ • b := by
        have : (φ c).out = g⁻¹ • Pc c := by rw [← hg, inv_smul_smul]
        rw [this, ← hPc c]
        exact TernaryPoly.SymmetricSpaceBoundaryFaceAugmentation.flagPlane_equivariant _ _
      rw [h1]
      exact (hS g⁻¹ b).2 hb
  rw [himg, Finset.sum_image (fun x _ y _ h => hinj h)]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := exists_conj_of_orbit (Pc c) (φ c) rfl
  have hF : (φ c).out = g⁻¹ • Pc c := by rw [← hg, inv_smul_smul]
  rw [planeFlagClass_conj π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he) (φ c) g⁻¹ (Pc c) hF, flagEval_lam_conj g⁻¹ (Pc c) (φ c) hF,
    planeFlag_coord_eq_clsRes π d e _ (cutγ_plane_primitive π d e γ hγ S hS hd he) (Pc c)]

end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
