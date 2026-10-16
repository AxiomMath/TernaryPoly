module

public import TernaryPeriodPolynomials.DifferentialForm.CochainComparison.Cone
public import TernaryPeriodPolynomials.EisensteinSeries.Class.Setup
public import TernaryPeriodPolynomials.EisensteinSeries.EisensteinClass

@[expose] public section


/-!
# The unimodular normalization `Gram cone → Ω` and the linear action of `Γ ⊂ SL₃(ℤ)` on the cone

Formalized by Claude Sonnet 5.5.
-/

open scoped Matrix.Norms.Elementwise ContDiff
open Set Matrix

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FormCochainBridge

open TernaryPeriodPolynomials.Argument.ConvergenceC4 TernaryPeriodPolynomials.Argument.SeedC3
  TernaryPeriodPolynomials.Argument.EisensteinClass

local notation "Mat3" => Matrix (Fin 3) (Fin 3) ℝ

/-- The symmetric part of a matrix. -/
def symPart (G : Mat3) : Mat3 := (1 / 2 : ℝ) • (G + G.transpose)

theorem symPart_isHermitian (G : Mat3) : (symPart G).IsHermitian := by
  ext i j
  simp [symPart, Matrix.conjTranspose_apply]
  ring

theorem posDef_symPart {G : Mat3} (hG : G ∈ gramCone) : (symPart G).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (symPart_isHermitian G) fun x hx => ?_
  have h := (mem_gramCone_iff.1 hG) x hx
  have e : x ⬝ᵥ (symPart G *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
    simp only [symPart, Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add]
    have : x ⬝ᵥ (G.transpose *ᵥ x) = x ⬝ᵥ (G *ᵥ x) := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
    rw [this]; simp; ring
  simpa [e] using h

/-- The unimodular normalization `(det S)^{-1/3} S` of a positive definite matrix. -/
def normGram (S : Mat3) : Mat3 := (S.det ^ (-(1 / 3 : ℝ))) • S

theorem isGram_normGram {S : Mat3} (hS : S.PosDef) : IsGram (normGram S) := by
  have hd : 0 < S.det := hS.det_pos
  have hc : 0 < S.det ^ (-(1 / 3 : ℝ)) := Real.rpow_pos_of_pos hd _
  refine ⟨hS.smul hc, ?_⟩
  unfold normGram
  rw [Matrix.det_smul, Fintype.card_fin]
  have : (S.det ^ (-(1 / 3 : ℝ))) ^ 3 = S.det⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]
    norm_num
    exact Real.rpow_neg_one S.det
  rw [this]
  exact inv_mul_cancel₀ hd.ne'

/-- The equivariant map `Gram cone → Ω`: unimodular normalization of the symmetric part, then the plane chart. -/
def conePoint (G : Mat3) : Fin 5 → ℝ := planePoint (normGram (symPart G))

theorem conePoint_mem {G : Mat3} (hG : G ∈ gramCone) : conePoint G ∈ Omega :=
  planePoint_mem (isGram_normGram (posDef_symPart hG))

/-- The linear map `G ↦ g G gᵀ`. -/
def conjCLM (g : Mat3) : Mat3 →L[ℝ] Mat3 :=
  LinearMap.toContinuousLinearMap ((LinearMap.mulLeft ℝ g).comp (LinearMap.mulRight ℝ g.transpose))

theorem conjCLM_apply (g G : Mat3) : conjCLM g G = g * G * g.transpose := by
  simp [conjCLM, Matrix.mul_assoc]

theorem conj_mem_gramCone {g G : Mat3} (hg : g.det = 1) (hG : G ∈ gramCone) :
    g * G * g.transpose ∈ gramCone := by
  rw [mem_gramCone_iff]
  intro x hx
  have hu : IsUnit g.transpose.det := by rw [Matrix.det_transpose, hg]; exact isUnit_one
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  have hy : g.transpose *ᵥ x ≠ 0 := fun h => hx (hinj (by simpa using h))
  have h := (mem_gramCone_iff.1 hG) _ hy
  have e : x ⬝ᵥ ((g * G * g.transpose) *ᵥ x) = (g.transpose *ᵥ x) ⬝ᵥ (G *ᵥ (g.transpose *ᵥ x)) := by
    rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose]
  rw [e]; exact h

theorem symPart_conj (g G : Mat3) : symPart (g * G * g.transpose) = g * symPart G * g.transpose := by
  simp only [symPart, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem normGram_conj {g : Mat3} (hg : g.det = 1) (S : Mat3) :
    normGram (g * S * g.transpose) = g * normGram S * g.transpose := by
  have hd : (g * S * g.transpose).det = S.det := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hg]; ring
  simp only [normGram, hd, Matrix.mul_smul, Matrix.smul_mul]

/-- **Equivariance of the normalization**: `conePoint (g G gᵀ) = g · conePoint G` for `g ∈ SL₃`. -/
theorem conePoint_conj {g G : Mat3} (hg : g.det = 1) (hG : G ∈ gramCone) :
    conePoint (g * G * g.transpose) = planeAct g (conePoint G) := by
  have hGr : IsGram (normGram (symPart G)) := isGram_normGram (posDef_symPart hG)
  unfold conePoint planeAct
  rw [planeGram_planePoint hGr, symPart_conj, normGram_conj hg]

theorem contDiff_det_symPart : ContDiff ℝ ⊤ (fun G : Mat3 => (symPart G).det) := by
  simp only [Matrix.det_fin_three, symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
  fun_prop

theorem contDiffOn_conePoint : ContDiffOn ℝ ∞ conePoint gramCone := by
  intro G hG
  have hP := posDef_symPart hG
  have hI := isGram_normGram hP
  have hd : 0 < (symPart G).det := hP.det_pos
  have hF : ∀ i j, ContDiffAt ℝ ⊤ (fun y : Mat3 => normGram (symPart y) i j) G := by
    intro i j
    have h1 : ContDiffAt ℝ ⊤ (fun y : Mat3 => (symPart y).det ^ (-(1 / 3 : ℝ))) G :=
      contDiff_det_symPart.contDiffAt.rpow_const_of_ne hd.ne'
    have h2 : ContDiffAt ℝ ⊤ (fun y : Mat3 => symPart y i j) G := by
      simp only [symPart, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply]
      fun_prop
    simpa [normGram] using h1.mul h2
  have := contDiffAt_planePoint_comp hF hI.s_pos hI.schur_pos
  exact (this.of_le le_top).contDiffWithinAt

/-- The linear action of `Γ ⊂ SL₃(ℤ)` on the Gram cone, `G ↦ γ G γᵀ`. -/
def coneAction (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) : ZigZag.Action Γ gramCone where
  act δ G := realMat δ.1 * G * (realMat δ.1).transpose
  smooth δ := (conjCLM (realMat δ.1)).contDiff.contDiffOn.congr (fun G _ => (conjCLM_apply _ _).symm)
  mapsTo δ _ hG := conj_mem_gramCone (det_realMat δ.1) hG
  mul δ ε G _ := by
    change realMat (δ.1 * ε.1) * G * (realMat (δ.1 * ε.1)).transpose =
      realMat δ.1 * (realMat ε.1 * G * (realMat ε.1).transpose) * (realMat δ.1).transpose
    simp [realMat_mul, Matrix.transpose_mul, Matrix.mul_assoc]

/-- The cone action is by globally defined linear maps. -/
def coneAffine (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) : AffineAction (coneAction Γ) where
  lin δ := conjCLM (realMat δ.1)
  off _ := 0
  act_eq δ G := by
    change realMat δ.1 * G * (realMat δ.1).transpose = conjCLM (realMat δ.1) G + 0
    rw [conjCLM_apply, add_zero]
  one G _ := by
    change realMat (1 : Γ).1 * G * (realMat (1 : Γ).1).transpose = G
    simp [realMat_one]

/-- The unimodular normalization is a `Γ`-equivariant smooth map from the Gram cone to `Ω`. -/
def coneEquiv (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) :
    EquivMap isOpen_gramCone isOpen_Omega (coneAction Γ) (gammaAct Γ) (MonoidHom.id Γ) where
  φ := conePoint
  smooth := contDiffOn_conePoint
  mapsTo _ hG := conePoint_mem hG
  equiv δ _ hG := conePoint_conj (det_realMat δ.1) hG

theorem gram_act_one (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) :
    (coneAction Γ).act 1 (1 : Mat3) = 1 := by
  change realMat (1 : Γ).1 * 1 * (realMat (1 : Γ).1).transpose = 1
  simp [realMat_one]

theorem gram_act_one_right (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) (a : Γ) :
    (coneAction Γ).act a (1 : Mat3) = realMat a.1 * (realMat a.1).transpose := by
  change realMat a.1 * 1 * (realMat a.1).transpose = _
  rw [Matrix.mul_one]

/-- **The Gram-triangle cochain.** For a closed `Γ`-equivariant `2`-form `ω` on the symmetric space chart `Ω`, the cocycle
`(a, b) ↦ ∫_{[1, a aᵀ, (ab)(ab)ᵀ]} φ^*ω` over the affine triangle of Gram matrices (`φ` the equivariant unimodular
normalization of the Gram cone) represents the de Rham class of `ω` in `H²(Γ, F)`. -/
theorem bridge_gram (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] (ρ : Representation ℝ Γ F)
    (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) :
    (groupCohomology.H2π (Rep.of ρ)).hom
        ⟨_, isCocycle_inhomTriangle isOpen_gramCone (coneAction Γ) ρ convex_gramCone ⟨1, one_mem_gramCone⟩
          (coneAffine Γ) (pullInv (coneEquiv Γ) (fun _ => rfl) om) one_mem_gramCone⟩ =
      ZigZag.deRhamClass isOpen_Omega convex_Omega Omega_nonempty (gammaAct Γ) ρ om :=
  bridge_pullback (coneAffine Γ) (coneEquiv Γ) convex_gramCone ⟨1, one_mem_gramCone⟩ convex_Omega
    Omega_nonempty om one_mem_gramCone

/-- The pullback `φ^*ω` of a closed equivariant form on `Ω` to the Gram cone, as a raw chart form. -/
def gramForm (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F] (ρ : Representation ℝ Γ F)
    (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) : TernaryPoly.SmoothLocalDeRham.RawForm Mat3 F 2 :=
  ((pullInv (coneEquiv Γ) (fun _ => rfl) om : ZigZag.invClosed isOpen_gramCone (coneAction Γ) ρ) :
    TernaryPoly.SmoothLocalDeRham.Form (F := F) gramCone 2)

/-- **Equivariance of the Gram-triangle cochain**: `F(γ y) = ρ(γ) F(y)`. -/
theorem gramTriangle_equivariant (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (ρ : Representation ℝ Γ F) (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) (g : Γ) (y : Fin 3 → Γ) :
    triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 (fun i => g * y i) =
      ρ g (triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 y) :=
  triangleCochain_equivariant isOpen_gramCone convex_gramCone (coneAffine Γ) ρ _ one_mem_gramCone g y

/-- **The Gram-triangle cochain is a homogeneous `2`-cocycle**. -/
theorem gramTriangle_isCocycle (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (ρ : Representation ℝ Γ F) (om : ZigZag.invClosed isOpen_Omega (gammaAct Γ) ρ) (x : Fin 4 → Γ) :
    triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 ![x 1, x 2, x 3] -
      triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 ![x 0, x 2, x 3] +
      triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 ![x 0, x 1, x 3] -
      triangleCochain (coneAction Γ)
        (gramForm Γ ρ om) 1 ![x 0, x 1, x 2] = 0 :=
  triangleCochain_isCocycle isOpen_gramCone convex_gramCone (coneAction Γ) _
    (pullInv (coneEquiv Γ) (fun _ => rfl) om).2.1 one_mem_gramCone x

/-- The cochain of `bridge_gram` is the Gram-triangle integral `∫_{[1, a aᵀ, (ab)(ab)ᵀ]} φ^*ω`. -/
theorem inhomTriangle_gram (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [CompleteSpace F]
    (w2 : TernaryPoly.SmoothLocalDeRham.RawForm Mat3 F 2) (a b : Γ) :
    inhomTriangle (coneAction Γ) w2 (1 : Mat3) a b =
      triInt w2 1 (realMat a.1 * (realMat a.1).transpose)
        (realMat (a * b).1 * (realMat (a * b).1).transpose) := by
  unfold inhomTriangle triangleCochain
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, gram_act_one_right]
  simp [realMat_one]

/-- **The class of the Eisenstein series `𝓔_P(ω_h)` is represented by its Gram-triangle cochain**
(OB5): the cocycle `(a, b) ↦ ∫_{[1, a aᵀ, (ab)(ab)ᵀ]} φ^*𝓔_P(ω_h)` of integrals over affine triangles of Gram
matrices has the literal class `eisensteinClass` of the series. -/
theorem bridge_eisenstein (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) ℤ)) {Fm : Type*} [FunLike Fm UpperHalfPlane ℂ]
    (Λ : Subgroup (GL (Fin 2) ℝ)) [Λ.HasDetOne] [Λ.IsArithmetic] (n : ℕ)
    [CuspFormClass Fm Λ ((n + 3 : ℕ) : ℤ)] (f : Fm) (hn : 4 ≤ n) (hLevi : LeviIn Γ Λ) :
    (groupCohomology.H2π (Rep.of (gammaRho Γ n))).hom
        ⟨_, isCocycle_inhomTriangle isOpen_gramCone (coneAction Γ) (gammaRho Γ n) convex_gramCone
          ⟨1, one_mem_gramCone⟩ (coneAffine Γ)
          (pullInv (coneEquiv Γ) (fun _ => rfl) (Statements.EisensteinClass.planeEisensteinInv Γ Λ n f hn hLevi))
          one_mem_gramCone⟩ =
      Statements.EisensteinClass.eisensteinClass Γ Λ n f hn hLevi :=
  bridge_gram Γ (gammaRho Γ n) (Statements.EisensteinClass.planeEisensteinInv Γ Λ n f hn hLevi)

end TernaryPeriodPolynomials.Argument.FormCochainBridge
