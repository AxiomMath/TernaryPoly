module

public import TernaryPeriodPolynomials.BoundaryComparison.SeriesModel.Statement
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.Plane.SourcePackage

@[expose] public section


/-!
# The Gram-triangle cochain on `GL₃(ℝ)`-vertices represents the complexified class

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise MatrixGroups ContDiff
open Matrix GeneralEisenstein GeneralEisenstein.Homogeneous

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormSeriesModel

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.EisensteinClass
  TernaryPeriodPolynomials.Argument.FormCochainBridge
  TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry TernaryPeriodPolynomials.Argument.SeedC3

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

theorem gramOf_mem_gramCone (y : RealGL3) : gramOf y ∈ gramCone := by
  rw [mem_gramCone_iff]
  intro x hx
  have := (Matrix.posDef_iff_dotProduct_mulVec.1 (posDef_gramOf y)).2 hx
  simpa using this

theorem gramOf_mul (g y : RealGL3) : gramOf (g * y) = g.val * gramOf y * g.val.transpose := by
  simp [gramOf, Matrix.mul_assoc, Matrix.transpose_mul]

theorem gramOf_one : gramOf (1 : RealGL3) = 1 := by simp [gramOf]

section Cochain

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)

/-- **The Gram-triangle cochain on `GL₃(ℝ)`-vertices**: `F(y₀,y₁,y₂) = ∫_{[y₀y₀ᵀ, y₁y₁ᵀ, y₂y₂ᵀ]} φ^*ω`. -/
def gramCochain (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)) (y : Fin 3 → RealGL3) :
    Coef n :=
  triInt (gramForm Γ (gammaRho Γ n) om) (gramOf (y 0)) (gramOf (y 1)) (gramOf (y 2))

/-- Equivariance of the triangle integral of the pulled-back form on arbitrary points of the cone. -/
theorem triInt_gramForm_equivariant (ρ : Representation ℝ Γ (Coef n))
    (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) (γ : Γ) {p₀ p₁ p₂ : Mat3}
    (h₀ : p₀ ∈ gramCone) (h₁ : p₁ ∈ gramCone) (h₂ : p₂ ∈ gramCone) :
    triInt (gramForm Γ ρ om) (realMat γ.1 * p₀ * (realMat γ.1).transpose)
        (realMat γ.1 * p₁ * (realMat γ.1).transpose) (realMat γ.1 * p₂ * (realMat γ.1).transpose) =
      ρ γ (triInt (gramForm Γ ρ om) p₀ p₁ p₂) := by
  have e := triInt_pullForm isOpen_gramCone convex_gramCone (coneAffine Γ) γ
    (((pullInv (coneEquiv Γ) (fun _ => rfl) om : ZigZag.invClosed isOpen_gramCone (coneAction Γ) ρ) :
      TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2)) h₀ h₁ h₂
  have h2 := (pullInv (coneEquiv Γ) (fun _ => rfl) om).2.2 γ
  have e2 := triInt_twForm (s := gramCone) convex_gramCone (ZigZag.repCLM ρ γ)
    (((pullInv (coneEquiv Γ) (fun _ => rfl) om : ZigZag.invClosed isOpen_gramCone (coneAction Γ) ρ) :
      TernaryPoly.SmoothLocalDeRham.Form (F := Coef n) gramCone 2)) h₀ h₁ h₂
  rw [h2] at e
  exact e.symm.trans e2

end Cochain

section Points

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] {s : Set E}

omit [FiniteDimensional ℝ F] in
/-- The triangle integrals of a closed `2`-form over the four faces of a tetrahedron of points of a convex open set cancel. -/
theorem triInt_cocycle_points (hs : IsOpen s) (hc : Convex ℝ s)
    (w2 : TernaryPoly.SmoothLocalDeRham.Form (F := F) s 2) (hw : TernaryPoly.SmoothLocalDeRham.d hs 2 w2 = 0)
    (p : Fin 4 → E) (hp : ∀ i, p i ∈ s) :
    triInt (w2 : TernaryPoly.SmoothLocalDeRham.RawForm E F 2) (p 1) (p 2) (p 3) -
        triInt (w2 : TernaryPoly.SmoothLocalDeRham.RawForm E F 2) (p 0) (p 2) (p 3) +
        triInt (w2 : TernaryPoly.SmoothLocalDeRham.RawForm E F 2) (p 0) (p 1) (p 3) -
        triInt (w2 : TernaryPoly.SmoothLocalDeRham.RawForm E F 2) (p 0) (p 1) (p 2) = 0 := by
  obtain ⟨η, hη⟩ := exists_edge_cochain hs hc w2 hw
  have key : ∀ a b c : Fin 4, triInt (w2 : TernaryPoly.SmoothLocalDeRham.RawForm E F 2) (p a) (p b) (p c) =
      segInt (η : TernaryPoly.SmoothLocalDeRham.RawForm E F 1) (p b) (p c) -
        segInt (η : TernaryPoly.SmoothLocalDeRham.RawForm E F 1) (p a) (p c) +
        segInt (η : TernaryPoly.SmoothLocalDeRham.RawForm E F 1) (p a) (p b) := by
    intro a b c
    rw [← hη]
    exact triInt_d_one hs hc η (hp a) (hp b) (hp c)
  rw [key 1 2 3, key 0 2 3, key 0 1 3, key 0 1 2]
  abel

end Points

section Bridge

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (n : ℕ)

/-- The image of `Γ ⊂ SL₃(ℤ)` in the ambient group `GL₃(ℝ)` of the homogeneous model. -/
def realLevel : Subgroup RealGL3 := Γ.map (Matrix.SpecialLinearGroup.mapGL ℝ)

/-- `Γ ≅ realLevel Γ`. -/
def realLevelHom : Γ →* realLevel Γ := (Matrix.SpecialLinearGroup.mapGL ℝ).subgroupMap Γ

theorem realLevelHom_val (γ : Γ) : ((realLevelHom Γ γ : realLevel Γ) : RealGL3) =
    Matrix.SpecialLinearGroup.mapGL ℝ γ.1 := rfl

theorem mapGL_val (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ γ : RealGL3) : Mat3) = realMat γ := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  ext i j
  simp [realMat]

/-- The Gram-triangle cochain is `realLevel`-equivariant for the complex coefficient representation. -/
theorem gramCochain_mem (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)) :
    (gramCochain Γ n om : (Fin 3 → RealGL3) → HomogeneousPoly n) ∈
      cochains (realLevel Γ) (GeneralEisenstein.realCoefficient n) 2 := by
  rintro ⟨_, γ, hγ, rfl⟩ x
  have hv : ∀ i, gramOf (Matrix.SpecialLinearGroup.mapGL ℝ γ * x i) =
      realMat γ * gramOf (x i) * (realMat γ).transpose := by
    intro i
    rw [gramOf_mul, mapGL_val]
  have := triInt_gramForm_equivariant Γ n (gammaRho Γ n) om ⟨γ, hγ⟩ (gramOf_mem_gramCone (x 0))
    (gramOf_mem_gramCone (x 1)) (gramOf_mem_gramCone (x 2))
  unfold gramCochain
  simp only [hv]
  exact this

/-- The Gram-triangle cochain as a homogeneous `2`-cocycle of the model. -/
def gramCocycle (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)) :
    cocycles (realLevel Γ) (GeneralEisenstein.realCoefficient n) :=
  ⟨⟨(gramCochain Γ n om : (Fin 3 → RealGL3) → HomogeneousPoly n), gramCochain_mem Γ n om⟩, by
    change differentialTwo (realLevel Γ) (GeneralEisenstein.realCoefficient n) _ = 0
    funext x
    exact triInt_cocycle_points isOpen_gramCone convex_gramCone _
      (pullInv (coneEquiv Γ) (fun _ => rfl) om).2.1 (fun i => gramOf (x i)) (fun i => gramOf_mem_gramCone (x i))⟩

/-- The comparison of coefficient modules `Γ ≅ realLevel Γ`. -/
def repMorReal : Rep.res (realLevelHom Γ)
    (Rep.of ((GeneralEisenstein.realCoefficient n).comp (realLevel Γ).subtype)) ⟶ gammaRep Γ n :=
  Rep.ofHom ⟨LinearMap.id, fun _ => LinearMap.ext fun _ => rfl⟩

/-- **Step 1+2: the Gram-triangle cochain on `GL₃(ℝ)`-vertices represents the complexified de Rham class.**
For every closed `Γ`-equivariant `2`-form `ω` on `Ω` with coefficients in the real representation `gammaRho Γ n`, the homogeneous
cocycle `F(y₀,y₁,y₂) = ∫_{[y_iy_iᵀ]} φ^*ω` of the model, under `LevelTransfer.bridge` and the identification `Γ ≅ realLevel Γ`, has the
complexified literal class of `ω`. -/
theorem bridge_gramCocycle (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) (gammaRho Γ n)) :
    (groupCohomology.map (realLevelHom Γ) (repMorReal Γ n) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (GeneralEisenstein.realCoefficient n) (realLevel Γ)
          (Submodule.Quotient.mk (gramCocycle Γ n om))) =
      complexify Γ n (ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) (gammaRho Γ n) om) := by
  rw [← bridge_gram Γ (gammaRho Γ n) om, complexify_H2π,
    TernaryPeriodPolynomials.Argument.LevelTransfer.bridge_mk, groupCohomology.H2π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext p
  obtain ⟨a, b⟩ := p
  have h1 : gramCochain Γ n om ![1, Matrix.SpecialLinearGroup.mapGL ℝ a.1,
      Matrix.SpecialLinearGroup.mapGL ℝ a.1 * Matrix.SpecialLinearGroup.mapGL ℝ b.1] =
      inhomTriangle (coneAction Γ) (gramForm Γ (gammaRho Γ n) om) 1 a b := by
    rw [inhomTriangle_gram]
    unfold gramCochain
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, gramOf, mapGL_val, ← map_mul]
    simp [Subgroup.coe_mul]
  exact h1

open TernaryPeriodPolynomials.Argument.Statements.EisensteinClass in
/-- **The class of `𝓔_P(ω_h)` is the bridge of the Gram-triangle cocycle on `GL₃(ℝ)`-vertices** (Steps 1-2 of OB7 route A). -/
theorem bridge_gramCocycle_eisenstein (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {Fm : Type*}
    [FunLike Fm UpperHalfPlane ℂ] (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
    [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] (f : Fm) (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    (groupCohomology.map (realLevelHom Γ) (repMorReal Γ n) 2).hom
        (TernaryPeriodPolynomials.Argument.LevelTransfer.bridge (GeneralEisenstein.realCoefficient n) (realLevel Γ)
          (Submodule.Quotient.mk (gramCocycle Γ n (planeEisensteinInv Γ Λ n f hn hLevi)))) =
      eisensteinClassC Γ Λ n f hn hLevi :=
  bridge_gramCocycle Γ n (planeEisensteinInv Γ Λ n f hn hLevi)

end Bridge

end TernaryPeriodPolynomials.Argument.FormSeriesModel
