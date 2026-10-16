module

public import TernaryPeriodPolynomials.BoundaryComparison.SeedForms.FaceMap
public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.CochainLedger
public import TernaryPeriodPolynomials.BoundaryComparison.SeedClasses.Descent.GammaNSeed

@[expose] public section


/-!
# The Gram-triangle cochain of the seed `ω_h` on `Γ_P = Γ(N) ∩ P(ℤ)` represents the seed class (G5, holomorphic half)

Formalized by Claude Sonnet 5.5.
Paper: Lemma C.3 (`ar:lem:seed`) and the unfolding of the
Eisenstein class at the plane cusp.

* `gramCochainW`, `gramCocycleW`: the Gram-triangle cochain `F(y₀,y₁,y₂) = ∫_{[y_iy_iᵀ]} W` of any invariant closed form `W` on the Gram cone
  is a homogeneous `2`-cocycle of the model on `GL₃(ℝ)`-vertices.
* `seedCone`: the seed `ω_h` of Lemma C.3 pulled back to the Gram cone along `coneFace` (`FaceMap.lean`).
* `seedCone_pair`, `coeff_gramCochainW_seed`, `planeIntG_one`: its coefficients are the library's plane integral cochain `planeIntG n h 1`.
* **`bridge_gramCocycleW_seed`**: under `LevelTransfer.bridge` and `Γ_P ≅ realLevel Γ_P` its class is `complexifyG N n (seedClass …)`.
* **`cOmegaCoeff_one_eq`**: the level-one scalar ledger relating the model's `cOmega` at the identity plane to it.
* `seedTri_translate_gl`, `planeIntG_eq_seedTri_gl`: the reflected half of `cOmega` as the `ρ(ε)⁻¹`-twisted seed cochain at the vertices `ε y_i`.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous MeasureTheory

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeedBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.SeedC3.Psi
  TernaryPeriodPolynomials.Argument.EisensteinClass TernaryPeriodPolynomials.Argument.FormCochainBridge
  TernaryPeriodPolynomials.Argument.FormSeriesModel
  TernaryPeriodPolynomials.Argument.SeedC3S4c
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

section Generic

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ) (ρ : Representation ℝ Γ (Coef n))
  (W : ZigZag.invClosed isOpen_gramCone (coneAction Γ) ρ)

/-- **The Gram-triangle cochain of an invariant closed form `W` on the Gram cone**, on `GL₃(ℝ)`-vertices. -/
def gramCochainW (y : Fin 3 → RealGL3) : Coef n :=
  triInt ((W : TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) :
    TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2))

theorem gramCochainW_equivariant (γ : Γ) {p₀ p₁ p₂ : Mat3}
    (h₀ : p₀ ∈ gramCone) (h₁ : p₁ ∈ gramCone) (h₂ : p₂ ∈ gramCone) :
    triInt ((W : TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) :
        TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) (realMat γ.1 * p₀ * (realMat γ.1).transpose)
        (realMat γ.1 * p₁ * (realMat γ.1).transpose) (realMat γ.1 * p₂ * (realMat γ.1).transpose) =
      ρ γ (triInt ((W : TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) :
        TernaryPoly.SmoothLocalDeRham.RawForm Mat3 (Coef n) 2) p₀ p₁ p₂) := by
  have e := triInt_pullForm isOpen_gramCone convex_gramCone (coneAffine Γ) γ
    (W : TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) h₀ h₁ h₂
  have h2 := W.2.2 γ
  have e2 := triInt_twForm (s := gramCone) convex_gramCone (ZigZag.repCLM ρ γ)
    (W : TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2) h₀ h₁ h₂
  rw [h2] at e
  exact e.symm.trans e2

variable {Γ n ρ}

theorem gramCochainW_mem (hρ : ∀ γ, ρ γ = gammaRho Γ n γ) :
    (gramCochainW Γ n ρ W : (Fin 3 → RealGL3) → HomogeneousPoly n) ∈
      cochains (realLevel Γ) (GeneralEisenstein.realCoefficient n) 2 := by
  rintro ⟨_, γ, hγ, rfl⟩ x
  have hv : ∀ i, gramOf (Matrix.SpecialLinearGroup.mapGL ℝ γ * x i) =
      realMat γ * gramOf (x i) * (realMat γ).transpose := by
    intro i
    rw [FormSeriesModel.gramOf_mul, mapGL_val]
  have := gramCochainW_equivariant Γ n ρ W ⟨γ, hγ⟩ (gramOf_mem_gramCone (x 0))
    (gramOf_mem_gramCone (x 1)) (gramOf_mem_gramCone (x 2))
  rw [hρ] at this
  unfold gramCochainW
  simp only [hv]
  exact this

/-- The Gram-triangle cochain of `W` as a homogeneous `2`-cocycle of the model. -/
def gramCocycleW (hρ : ∀ γ, ρ γ = gammaRho Γ n γ) :
    cocycles (realLevel Γ) (GeneralEisenstein.realCoefficient n) :=
  ⟨⟨(gramCochainW Γ n ρ W : (Fin 3 → RealGL3) → HomogeneousPoly n), gramCochainW_mem W hρ⟩, by
    change differentialTwo (realLevel Γ) (GeneralEisenstein.realCoefficient n) _ = 0
    funext x
    exact triInt_cocycle_points isOpen_gramCone convex_gramCone _
      W.2.1 (fun i => gramOf (x i)) (fun i => gramOf_mem_gramCone (x i))⟩

end Generic

/-- Bilinear expansion of an alternating `2`-form on `ℝ⁴` along the coordinate basis. -/
theorem alt2_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : (Fin 4 → ℝ) [⋀^Fin 2]→L[ℝ] F) (a b : Fin 4 → ℝ) :
    w ![a, b] = ∑ i, ∑ j, (a i * b j) • w ![Pi.single i 1, Pi.single j 1] := by
  have hb : b = ∑ j, b j • (Pi.single j 1 : Fin 4 → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have ha : a = ∑ i, a i • (Pi.single i 1 : Fin 4 → ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have h2 : ∀ (x : Fin 4 → ℝ), w ![x, b] = ∑ j, b j • w ![x, Pi.single j 1] := by
    intro x
    let L : (Fin 4 → ℝ) →ₗ[ℝ] F := w.toContinuousMultilinearMap.toMultilinearMap.toLinearMap ![x, 0] 1
    have hL : ∀ y, L y = w ![x, y] := by
      intro y
      have e : Function.update ![x, 0] 1 y = ![x, y] := by
        funext k; fin_cases k <;> simp
      simp only [L, MultilinearMap.toLinearMap_apply]
      exact congrArg w.toContinuousMultilinearMap.toMultilinearMap e
    have h := congrArg L hb
    rw [hL] at h
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hL]
  have h1 : w ![a, b] = ∑ i, a i • w ![Pi.single i 1, b] := by
    let L : (Fin 4 → ℝ) →ₗ[ℝ] F := w.toContinuousMultilinearMap.toMultilinearMap.toLinearMap ![0, b] 0
    have hL : ∀ y, L y = w ![y, b] := by
      intro y
      have e : Function.update ![0, b] 0 y = ![y, b] := by
        funext k; fin_cases k <;> simp
      simp only [L, MultilinearMap.toLinearMap_apply]
      exact congrArg w.toContinuousMultilinearMap.toMultilinearMap e
    have h := congrArg L ha
    rw [hL] at h
    rw [h, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hL]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h2, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]


section Seed

open TernaryPoly.SmoothLocalDeRham TernaryPoly.SmoothCoveringDeRham

/-- The projection `ℝ⁵ → ℝ⁴` onto the first four coordinates, as a continuous linear map. -/
def pr4CLM : (Fin 5 → ℝ) →L[ℝ] Face :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 0, ContinuousLinearMap.proj 1,
    ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

theorem pr4_apply (p : Fin 5 → ℝ) (i : Fin 4) : pr4 p i = p i.castSucc := by
  fin_cases i <;> rfl

theorem pr4CLM_apply (p : Fin 5 → ℝ) : pr4CLM p = pr4 p := by
  funext i; fin_cases i <;> rfl

theorem fderiv_coneFace {x : Mat3} (hx : x ∈ gramCone) (u : Mat3) :
    fderiv ℝ coneFace x u = pr4 (fderiv ℝ conePoint x u) := by
  have hd : DifferentiableAt ℝ conePoint x :=
    ((contDiffOn_conePoint x hx).contDiffAt (isOpen_gramCone.mem_nhds hx)).differentiableAt (by simp)
  have hc : coneFace = fun G => pr4CLM (conePoint G) := by
    funext G; exact (pr4CLM_apply _).symm
  have h2 : HasFDerivAt (fun G => pr4CLM (conePoint G)) (pr4CLM.comp (fderiv ℝ conePoint x)) x :=
    pr4CLM.hasFDerivAt.comp x hd.hasFDerivAt
  rw [hc, h2.fderiv]
  exact pr4CLM_apply _

variable (N : ℕ) (n : ℕ) (h : ℂ → ℂ) (Gm : ℕ → ℂ → ℂ)
  (hh : DifferentiableOn ℂ h Psi.upperSet)
  (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (h z * z ^ j) z)
  (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
    h (mob ((gammaNPlaneData N).lam g) z) = dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * h z)

/-- **The seed `ω_h` pulled back to the Gram cone** along the equivariant map `coneFace : Gram cone → e(P)`. -/
def seedCone : ZigZag.invClosed isOpen_gramCone (coneAction (gammaNP N)) ((gammaNPlaneData N).rhoR n) :=
  pullInv (coneFaceEquiv N) (fun _ => rfl) ((gammaNPlaneData N).seedInv h n Gm hh hG hmod)

omit hh hG hmod in
theorem rhoR_gammaNP (g : ↥(gammaNP N)) :
    (gammaNPlaneData N).rhoR n g = gammaRho (gammaNP N) n g :=
  rhoR_eq_gammaRho (gammaNPlaneData N) (MonoidHom.id _) (fun g => gammaNPlaneData_plm N g) g

theorem seedCone_pair_coef {x : Mat3} (hx : x ∈ gramCone) (u v : Mat3) :
    (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) : RawForm Mat3 (Coef n) 2) x) ![u, v] =
      (((gammaNPlaneData N).seedInv h n Gm hh hG hmod : Form (F := Coef n) faceSet 2) : RawForm Face (Coef n) 2)
        (coneFace x) ![fderiv ℝ coneFace x u, fderiv ℝ coneFace x v] := by
  change (pullBack isOpen_gramCone (coneFaceEquiv N).smooth (coneFaceEquiv N).mapsTo 2
    (((gammaNPlaneData N).seedInv h n Gm hh hG hmod : ZigZag.invClosed isOpen_faceSet _ _) :
      Form (F := Coef n) faceSet 2) : RawForm Mat3 (Coef n) 2) x ![u, v] = _
  rw [pullBack_apply isOpen_gramCone (coneFaceEquiv N).smooth (coneFaceEquiv N).mapsTo _ hx]
  unfold pullRaw
  rw [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have e : (⇑(fderiv ℝ (coneFaceEquiv N).φ x) ∘ ![u, v]) = ![fderiv ℝ coneFace x u, fderiv ℝ coneFace x v] := by
    funext i; fin_cases i <;> rfl
  exact congrArg (fun a => (((gammaNPlaneData N).seedInv h n Gm hh hG hmod : Form (F := Coef n) faceSet 2) :
    RawForm Face (Coef n) 2) (coneFace x) a) e

theorem seedInv_pair {z : Face} (hz : z ∈ faceSet) (a b : Face) :
    Coef.toPoly ((((gammaNPlaneData N).seedInv h n Gm hh hG hmod : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) z ![a, b]) =
      ∑ i : Fin 4, ∑ j : Fin 4, MvPolynomial.C ((a i * b j : ℝ) : ℂ) *
        seedForm n h (ptOf z) i.castSucc j.castSucc := by
  rw [alt2_expand, toPoly_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [toPoly_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.coe_smul, Coef.toPoly_smul]
  have := PlaneData.toPoly_d_etaForm h n hh hz i j
  rw [show ((((gammaNPlaneData N).seedInv h n Gm hh hG hmod : Form (F := Coef n) faceSet 2) :
        RawForm Face (Coef n) 2) z ![Pi.single i 1, Pi.single j 1]).toPoly = _ from this]

theorem seedCone_pair {x : Mat3} (hx : x ∈ gramCone) (u v : Mat3) :
    Coef.toPoly ((((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) :
        RawForm Mat3 (Coef n) 2) x) ![u, v]) =
      ∑ k : Fin 5, ∑ l : Fin 5, MvPolynomial.C ((fderiv ℝ conePoint x u k * fderiv ℝ conePoint x v l : ℝ) : ℂ) *
        seedForm n h (conePoint x) k l := by
  rw [seedCone_pair_coef N n h Gm hh hG hmod hx, seedInv_pair N n h Gm hh hG hmod (coneFace_mem hx)]
  have l4 : (Fin.last 4 : Fin 5) = 4 := rfl
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [l4, seedForm_four_left, mul_zero, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Fin.sum_univ_castSucc]
  simp only [l4, seedForm_four_right, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_coneFace hx, fderiv_coneFace hx]
  have hp : ∀ k : Fin 5, k ≠ 4 → ptOf (coneFace x) k = conePoint x k := by
    intro k hk
    fin_cases k <;> simp_all [ptOf, coneFace, pr4]
  rw [seedForm_congr n h hp, pr4_apply, pr4_apply]

/-- The seed form on the cone, coefficient `m` of the Gram-triangle cochain (`seedTri` is the integrand). -/
theorem coeff_gramCochainW_seed (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    (Coef.toPoly (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
        (seedCone N n h Gm hh hG hmod) y)).coeff m =
      ∫ q in stdTriangle, (seedTri n h y q).coeff m := by
  classical
  let Cℂ : Coef n →ₗ[ℂ] ℂ := (MvPolynomial.lcoeff ℂ m).comp (Submodule.subtype _)
  let CR : Coef n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Cℂ.restrictScalars ℝ)
  have hCR : ∀ z : Coef n, CR z = (Coef.toPoly z).coeff m := fun z => rfl
  set p0 := gramOf (y 0) with hp0
  set p1 := gramOf (y 1) with hp1
  set p2 := gramOf (y 2) with hp2
  have hc0 : p0 ∈ gramCone := gramOf_mem_gramCone (y 0)
  have hc1 : p1 ∈ gramCone := gramOf_mem_gramCone (y 1)
  have hc2 : p2 ∈ gramCone := gramOf_mem_gramCone (y 2)
  have hpt : ∀ q ∈ stdTriangle, affTri p0 p1 p2 q ∈ gramCone := fun q hq =>
    affTri_mem convex_gramCone hc0 hc1 hc2 hq
  have hint : IntegrableOn (fun q => (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) :
      RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q)) ![p1 - p0, p2 - p0]) stdTriangle :=
    integrable_triInt convex_gramCone
      ((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2)) hc0 hc1 hc2
  rw [← hCR]
  change CR (∫ q in stdTriangle, (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) :
      RawForm Mat3 (Coef n) 2) (affTri p0 p1 p2 q)) ![p1 - p0, p2 - p0]) = _
  rw [← ContinuousLinearMap.integral_comp_comm CR hint]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun q hq => ?_
  rw [hCR, seedCone_pair N n h Gm hh hG hmod (hpt q hq)]
  unfold seedTri
  rw [MvPolynomial.coeff_sum]

theorem planeIntG_one (y : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    planeIntG n h (realMat (1 : Matrix.SpecialLinearGroup (Fin 3) ℤ)) (gramOf (y 0)) (gramOf (y 1))
        (gramOf (y 2)) m = ∫ q in stdTriangle, (seedTri n h y q).coeff m := by
  rw [planeIntG_eq_seedTri]
  refine setIntegral_congr_fun measurableSet_stdTriangle fun q _ => ?_
  have e : (fun i => Matrix.SpecialLinearGroup.mapGL ℝ (1 : Matrix.SpecialLinearGroup (Fin 3) ℤ) * y i) = y := by
    funext i; simp
  rw [e, realMat_one, inv_one, rho_one]

theorem sigma_gammaNP (g : ↥(gammaNP N)) :
    (gammaNPlaneData N).sigma g = Matrix.SpecialLinearGroup.mapGL ℝ g.1 :=
  Units.ext (by rw [PlaneData.sigma_val, gammaNPlaneData_plm, mapGL_val])

/-- The comparison of coefficient modules for `Γ_P ≅ realLevel Γ_P`. -/
def repMorRealG : Rep.res (realLevelHom (gammaNP N))
    (Rep.of ((GeneralEisenstein.realCoefficient n).comp (realLevel (gammaNP N)).subtype)) ⟶
      gammaNRep N n :=
  Rep.ofHom ⟨LinearMap.id, fun g => LinearMap.ext fun v =>
    congrArg (fun γ => GeneralEisenstein.realCoefficient n γ v) (sigma_gammaNP N g).symm⟩

open TernaryPeriodPolynomials.Argument.LevelTransfer in
/-- **G5, holomorphic half (class level).**  For every holomorphic `h` on the upper half plane with the Levi modularity of
`Γ_P = Γ(N) ∩ P(ℤ)` and moment primitives `Gm`, the Gram-triangle cocycle of the pulled-back seed `ω_h` on `GL₃(ℝ)`-vertices
(coefficients: `planeIntG n h 1` of the library, `coeff_gramCochainW_seed`, `planeIntG_one`) has, under `LevelTransfer.bridge`
and `Γ_P ≅ realLevel Γ_P`, the complexified seed class of Lemma C.3 (`bridge_pullback` + `deRhamClass_seedInv`). -/
theorem bridge_gramCocycleW_seed [NeZero N] :
    (groupCohomology.map (realLevelHom (gammaNP N)) (repMorRealG N n) 2).hom
        (bridge (GeneralEisenstein.realCoefficient n) (realLevel (gammaNP N))
          (Submodule.Quotient.mk (gramCocycleW (seedCone N n h Gm hh hG hmod) (rhoR_gammaNP N n)))) =
      complexifyG N n ((gammaNPlaneData N).seedClass h n Gm hh hG hmod) := by
  rw [← PlaneData.deRhamClass_seedInv (gammaNPlaneData N) h n Gm hh hG hmod,
    ← bridge_pullback (coneAffine (gammaNP N)) (coneFaceEquiv N) convex_gramCone ⟨1, one_mem_gramCone⟩
      convex_faceSet faceSet_nonempty ((gammaNPlaneData N).seedInv h n Gm hh hG hmod) one_mem_gramCone,
    complexifyG_H2π, bridge_mk, groupCohomology.H2π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  have h1 : gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n) (seedCone N n h Gm hh hG hmod)
      ![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
        Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] =
      inhomTriangle (coneAction (gammaNP N))
        (((seedCone N n h Gm hh hG hmod : Form (F := Coef n) gramCone 2) : RawForm Mat3 (Coef n) 2)) 1 a b := by
    rw [inhomTriangle_gram]
    unfold gramCochainW
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, gramOf, mapGL_val, ← map_mul]
    simp [Subgroup.coe_mul]
  exact h1

open TernaryPeriodPolynomials.Argument GeneralEisenstein.Adelic
  TernaryPeriodPolynomials.SourceConstruction in
/-- **G5, level one, scalar ledger (cochain level).**  At the identity plane of the model (`g = 1`), with `H = F(1 · b_F(1))` the
scalar function of the holomorphic half, the coefficient of the plane integral cochain `cOmega n D F y 1` is `K` times the sum of
(i) the coefficient of the Gram-triangle cochain of the seed `ω_H` on `Γ_P = Γ(N) ∩ P(ℤ)` (whose class is the seed class,
`bridge_gramCocycleW_seed`), and (ii) the `J`-reflected half `planeIntG n H' ε …`, `H' = F(J · b_F(1))`, `ε = diag(-1,1,1)`;
`K = (-1)ⁿ (n+1) c_F(1) / 2`. -/
theorem cOmegaCoeff_one_eq (D : InducingData n) (F : BinaryAdelicGL → ℂ → ℂ)
    (hh : DifferentiableOn ℂ (F (1 * bF (1 : AdelicGL))) Psi.upperSet)
    (hG : ∀ j z, 0 < z.im → HasDerivAt (Gm j) (F (1 * bF (1 : AdelicGL)) z * z ^ j) z)
    (hmod : ∀ g : ↥(gammaNP N), ∀ z : ℂ, 0 < z.im →
      F (1 * bF (1 : AdelicGL)) (mob ((gammaNPlaneData N).lam g) z) =
        dnm ((gammaNPlaneData N).lam g) z ^ (n + 3) * F (1 * bF (1 : AdelicGL)) z)
    (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    cOmegaCoeff n D F y 1 κ =
      (((-1) ^ n * ((n + 1 : ℕ) : ℂ) * 2⁻¹) * cF D 1) *
        ((Coef.toPoly (gramCochainW (gammaNP N) n ((gammaNPlaneData N).rhoR n)
            (seedCone N n (F (1 * bF (1 : AdelicGL))) Gm hh hG hmod) y)).coeff κ +
          planeIntG n (F (atInfinity UpperHalfPlane.J * bF 1)) (epsJ.val * (realGroup (1 : AdelicGL)).val)
            (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ) := by
  rw [cOmegaCoeff_eq, coeff_gramCochainW_seed]
  have e : (realGroup (1 : AdelicGL)).val = realMat (1 : Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
    rw [map_one, Units.val_one, realMat_one]
  rw [e, planeIntG_one]

/-- **`seedTri` at the vertices `g y_i`, `g ∈ GL₃(ℝ)`, is the library's `twPull`-integrand `formPair`** (the same statement as
`seedTri_translate` for an arbitrary invertible real matrix, e.g. the reflection `ε`). -/
theorem seedTri_translate_gl (g : RealGL3) (y : Fin 3 → RealGL3) {q : ℝ × ℝ} (hq : q ∈ stdTriangle) :
    seedTri n h (fun i => g * y i) q =
      formPair (seedForm n h) (g.val * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * g.val.transpose)
        (g.val * (gramOf (y 1) - gramOf (y 0)) * g.val.transpose)
        (g.val * (gramOf (y 2) - gramOf (y 0)) * g.val.transpose) := by
  have e1 : ∀ i, gramOf (g * y i) = g.val * gramOf (y i) * g.val.transpose := fun i => FormSeriesModel.gramOf_mul g (y i)
  have haff : affTri (g.val * gramOf (y 0) * g.val.transpose)
      (g.val * gramOf (y 1) * g.val.transpose) (g.val * gramOf (y 2) * g.val.transpose) q =
      g.val * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * g.val.transpose := by
    simp only [affTri]
    simp only [← FormCochainBridge.conjCLM_apply, map_add, map_smul, map_sub]
  have hdiff : ∀ i j, g.val * gramOf (y i) * g.val.transpose -
      g.val * gramOf (y j) * g.val.transpose =
      g.val * (gramOf (y i) - gramOf (y j)) * g.val.transpose := by
    intro i j; simp [Matrix.mul_sub, Matrix.sub_mul]
  have hcone : g.val * affTri (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) q * g.val.transpose ∈ gramCone := by
    rw [← haff, ← e1 0, ← e1 1, ← e1 2]
    exact affTri_mem convex_gramCone (gramOf_mem_gramCone _) (gramOf_mem_gramCone _) (gramOf_mem_gramCone _) hq
  have hsy : ∀ i j, (gramOf (y i) - gramOf (y j)).IsSymm := by
    intro i j; unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, isSymm_gramOf, isSymm_gramOf]
  unfold seedTri
  simp only [e1, haff, hdiff]
  exact seed_cone_eq_formPair n h hcone
    (isSymm_conj (isSymm_affTri (isSymm_gramOf _) (isSymm_gramOf _) (isSymm_gramOf _) q))
    (isSymm_conj (hsy 1 0)) (isSymm_conj (hsy 2 0))

/-- **`planeIntG` at an arbitrary `M = g ∈ GL₃(ℝ)` is the `ρ(g)⁻¹`-twisted seed Gram-triangle cochain at the translated vertices `g y_i`**
(for `g = ε`: the reflected half of `cOmega`, R1c at the cochain level). -/
theorem planeIntG_eq_seedTri_gl (g : RealGL3) (y : Fin 3 → RealGL3) (κ : Fin 3 →₀ ℕ) :
    planeIntG n h g.val (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2)) κ =
      ∫ q in stdTriangle, (rho g.val⁻¹ (seedTri n h (fun i => g * y i) q)).coeff κ := by
  unfold planeIntG
  refine setIntegral_congr_fun measurableSet_stdTriangle fun q hq => ?_
  rw [seedTri_translate_gl n h g y hq]
  rfl

end Seed

end TernaryPeriodPolynomials.Argument.FormSeedBridge
