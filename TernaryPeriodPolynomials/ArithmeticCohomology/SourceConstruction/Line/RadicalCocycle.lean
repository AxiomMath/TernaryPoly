module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SourceConstruction.Line.RadicalBlock
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section


/-!
# The radical cocycle of the real line parabolic

Let `ι = lineEmbed : ℂ[y₀, y₁] → ℂ[x₀, x₁, x₂]` be the renaming `y_i ↦ x_{i+1}` (binary forms in
the two variables fixed by the line radical).  For `p = [[d, v], [0, A]]` in the real line
parabolic let `lrC(p) = (lrC0 p, lrC1 p) ∈ ℝ²` be the radical coordinates of
`LineRadicalBlock.lean` and put, for a binary form `Q` of degree `n + 1`,

`lineRadical n χ p Q := ι ( lrC0(p) ∂₀ Q + lrC1(p) ∂₁ Q )`  (a form of degree `n`, free of `x₀`).

For `u = lineUnipotent s t` this is `ι (t ∂₀ Q - s ∂₁ Q)` (`coe_lineRadical_unipotent`).

## The module the Levi part acts on

`lineStar χ k` is the representation of the real line parabolic on `Binary.HomogeneousPoly k` with

`(p ⋆ Q)(y) = χ(p) · d_p⁻² · Q(A_p⁻¹ y)`,  equivalently
`lineStar χ k p = θ(p) • Binary.homogeneousAction k (-1) (A_p)` with
`θ(p) = χ(p) · d_p⁻² · det A_p`   (`lineTheta`).

Here `χ(p) = componentCharacter χ p` and `d_p = p₀₀`, `A_p` the lower right `2 × 2` block.  This is
the scalar twist of the standard action for which the radical is a genuine cocycle:
`lineRadical_mul` says that for `n = k - 1`

`lineRadical n χ (p₁ p₂) Q = lineRadical n χ p₁ Q +
  realCoefficientComponent n χ p₁ (lineRadical n χ p₂ (lineStar χ (n+1) p₁⁻¹ Q))`,

the cocycle identity for the conjugation action `(p · L)(Q) = ρ(p) (L (p⁻¹ ⋆ Q))` on `Hom(Q, V)`,
and `lineRadical_levi_eq_zero` says the cocycle vanishes on the Levi subgroup.  The class of the
radical is the Kostant class `H¹(u, V) ≅ Sym^{n+1}(x₁, x₂) ⊗ (character)`: for a form `Q`,
`x₁ ∂₁Q + x₂ ∂₂Q = (n+1) Q` (Euler), so the radical at `s = 0` and `t = 1` is `∂₀ Q` and at `s = 1`,
`t = 0` is `-∂₁ Q` (the Koszul splitting `(c₁, c₂) = (-∂₂, ∂₁)Q / (n+1)` of `x₁ c₂ - x₂ c₁ = Q`).
The twist `χ(p) d_p⁻²` of `⋆` (positive scalar `d_p⁻²` on the Levi factor `GL₁`) and the factor
`det A_p` relative to the standard `det⁻¹`-twisted action are forced by the cocycle identity and
cannot be absorbed into the Levi cocycle of the `GL₂` factor.  They match the induction law of the
line side at the cohomological point `s = -3/2`: there `inductionExponent .line s = 1`, so
sections satisfy `f(lineLevi t 1 · g) = χ(t) |t|² f(g)` (the `|t|²` cancels `d_p⁻²`) and the cusp
condition carries `|det A|^{-(n+1)/2}` where the plane side has `|det A|^{-(n+3)/2}` (the extra
`|det A|` is the `det A_p` inside `θ`).  So after these normalizations the `GL₂` part of `⋆` is
`Binary.homogeneousAction (n+1) (-1) A_p` up to the sign character `χ(p)`, i.e. the module of the
Eichler cocycle of `EichlerCocycle.lean`, and the line source cocycle can reuse that Levi cocycle.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open MvPolynomial Matrix GeneralEisenstein
open GeneralEisenstein.Adelic
  (InLineParabolic lineParabolic lineUnipotent lineLevi lineLevi_mem lineLevi_val inLine_inv)

namespace TernaryPeriodPolynomials.SourceConstruction

/-! ## The vector field `a ∂₀ + b ∂₁` on binary polynomials -/

/-- The first order operator `a ∂₀ + b ∂₁` on binary polynomials. -/
def lrVecDeriv (a b : ℂ) (F : Binary.Poly) : Binary.Poly :=
  C a * pderiv (0 : Fin 2) F + C b * pderiv (1 : Fin 2) F

theorem lrVecDeriv_add (a b : ℂ) (F G : Binary.Poly) :
    lrVecDeriv a b (F + G) = lrVecDeriv a b F + lrVecDeriv a b G := by
  simp only [lrVecDeriv, map_add]
  ring

theorem lrVecDeriv_smul (a b c : ℂ) (F : Binary.Poly) :
    lrVecDeriv a b (c • F) = c • lrVecDeriv a b F := by
  simp only [lrVecDeriv, smul_eq_C_mul, pderiv_C_mul]
  ring

theorem lrVecDeriv_scale (c a b : ℂ) (F : Binary.Poly) :
    lrVecDeriv (c * a) (c * b) F = c • lrVecDeriv a b F := by
  unfold lrVecDeriv
  rw [smul_eq_C_mul, C_mul, C_mul]
  ring

theorem lrVecDeriv_isHomogeneous (a b : ℂ) {F : Binary.Poly} {n : ℕ}
    (hF : F.IsHomogeneous (n + 1)) : (lrVecDeriv a b F).IsHomogeneous n := by
  have h0 : (pderiv (0 : Fin 2) F).IsHomogeneous n := by
    have h := hF.pderiv (i := (0 : Fin 2))
    rwa [Nat.add_sub_cancel] at h
  have h1 : (pderiv (1 : Fin 2) F).IsHomogeneous n := by
    have h := hF.pderiv (i := (1 : Fin 2))
    rwa [Nat.add_sub_cancel] at h
  exact (h0.C_mul a).add (h1.C_mul b)

/-- Renamed vector fields subtract coefficientwise. -/
theorem lr_rename_vecDeriv_sub (a b a' b' : ℂ) (F : Binary.Poly) :
    rename (Fin.succ : Fin 2 → Fin 3) (lrVecDeriv a b F) -
        rename (Fin.succ : Fin 2 → Fin 3) (lrVecDeriv a' b' F) =
      rename (Fin.succ : Fin 2 → Fin 3) (lrVecDeriv (a - a') (b - b') F) := by
  simp only [lrVecDeriv, map_add, map_mul, map_sub, rename_C]
  ring

/-! ## The chain rule for binary substitution -/

theorem lr_substitute_C (M : Matrix (Fin 2) (Fin 2) ℂ) (c : ℂ) :
    Binary.substitute M (C c) = C c := by
  simp [Binary.substitute]

/-- The chain rule for a linear substitution of binary polynomials. -/
theorem lr_pderiv_substitute (N : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) (k : Binary.Poly) :
    pderiv j (Binary.substitute N k) = ∑ l, C (N l j) * Binary.substitute N (pderiv l k) := by
  induction k using MvPolynomial.induction_on with
  | C a => simp [Binary.substitute]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have hlin : pderiv j (Binary.linearForm N n) = C (N n j) := by
      unfold Binary.linearForm
      rw [Fin.sum_univ_two, map_add, pderiv_C_mul, pderiv_C_mul]
      fin_cases j <;> simp [pderiv_X]
    have hs : ∑ l, C (N l j) * Binary.substitute N (p * pderiv l (X n)) =
        Binary.substitute N p * C (N n j) := by
      rw [Finset.sum_eq_single n]
      · rw [pderiv_X_self, mul_one, mul_comm]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl), mul_zero, map_zero, mul_zero]
      · simp
    rw [map_mul, Binary.substitute_X, pderiv_mul, hlin, hp, ← hs, Finset.sum_mul,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [pderiv_mul, map_add, map_mul (Binary.substitute N) (pderiv l p) (X n),
      Binary.substitute_X]
    ring

/-- A vector field intertwines with a linear substitution through the matrix of the substitution. -/
theorem lrVecDeriv_substitute (M : Matrix (Fin 2) (Fin 2) ℂ) (a b : ℂ) (F : Binary.Poly) :
    lrVecDeriv a b (Binary.substitute M F) =
      Binary.substitute M
        (lrVecDeriv (M 0 0 * a + M 0 1 * b) (M 1 0 * a + M 1 1 * b) F) := by
  unfold lrVecDeriv
  rw [lr_pderiv_substitute, lr_pderiv_substitute, Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [map_add, map_mul, lr_substitute_C]
  ring

theorem lr_smul_rename_substitute_vecDeriv (B : Matrix (Fin 2) (Fin 2) ℂ) (c a b : ℂ)
    (F : Binary.Poly) :
    c • rename (Fin.succ : Fin 2 → Fin 3) (Binary.substitute B (lrVecDeriv a b F)) =
      rename (Fin.succ : Fin 2 → Fin 3) (Binary.substitute B (lrVecDeriv (c * a) (c * b) F)) := by
  rw [lrVecDeriv_scale, map_smul, map_smul]

/-! ## Substitution on forms free of `x₀` -/

/-- Substitution by a matrix with zero lower-left column acts on `x₀`-free polynomials through its
lower right block. -/
theorem lr_substitute_rename_succ (N : Matrix (Fin 3) (Fin 3) ℂ) (h : ∀ i : Fin 2, N i.succ 0 = 0)
    (G : Binary.Poly) :
    substitute N (rename (Fin.succ : Fin 2 → Fin 3) G) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (Binary.substitute (Matrix.of fun i j : Fin 2 => N i.succ j.succ) G) := by
  have key : (substitute N).comp (rename (Fin.succ : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly) =
      (rename (Fin.succ : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly).comp
        (Binary.substitute (Matrix.of fun i j : Fin 2 => N i.succ j.succ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, substitute_X, Binary.substitute_X, linearForm,
      Binary.linearForm, map_sum, map_mul, rename_C, Matrix.of_apply]
    rw [Fin.sum_univ_succ, h i, map_zero, zero_mul, zero_add]
  exact AlgHom.congr_fun key G

/-- The embedding `ℂ[y₀, y₁] → ℂ[x₀, x₁, x₂]`, `y_i ↦ x_{i+1}`, of binary forms of degree `k`. -/
def lineEmbed (k : ℕ) : Binary.HomogeneousPoly k →ₗ[ℂ] Poly :=
  (rename (Fin.succ : Fin 2 → Fin 3) : Binary.Poly →ₐ[ℂ] Poly).toLinearMap ∘ₗ
    Submodule.subtype _

theorem lineEmbed_apply (k : ℕ) (Q : Binary.HomogeneousPoly k) :
    lineEmbed k Q = rename (Fin.succ : Fin 2 → Fin 3) (Q : Binary.Poly) := rfl

/-! ## The radical -/

/-- The unnormalized radical: `ι (lrC0(p) ∂₀ Q + lrC1(p) ∂₁ Q)`, a form of degree `n`. -/
def lineRadAt (n : ℕ) (p : lineParabolic ℝ) (Q : Binary.HomogeneousPoly (n + 1)) :
    HomogeneousPoly n :=
  ⟨rename (Fin.succ : Fin 2 → Fin 3)
      (lrVecDeriv (algebraMap ℝ ℂ (lrC0 p)) (algebraMap ℝ ℂ (lrC1 p)) (Q : Binary.Poly)), by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact IsHomogeneous.rename_isHomogeneous (f := (Fin.succ : Fin 2 → Fin 3))
      (lrVecDeriv_isHomogeneous _ _ ((MvPolynomial.mem_homogeneousSubmodule _ _).mp Q.2))⟩

theorem coe_lineRadAt (n : ℕ) (p : lineParabolic ℝ) (Q : Binary.HomogeneousPoly (n + 1)) :
    (lineRadAt n p Q : Poly) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (lrVecDeriv (algebraMap ℝ ℂ (lrC0 p)) (algebraMap ℝ ℂ (lrC1 p)) (Q : Binary.Poly)) := rfl

/-- **The radical cocycle of the real line parabolic.**  `lineRadical n χ p` is the linear map
`Q ↦ ι (lrC0(p) ∂₀ Q + lrC1(p) ∂₁ Q)` from binary forms of degree `n + 1` to ternary forms of
degree `n` (free of `x₀`).  It does not depend on `χ`; the argument records the character of the
coefficient representation that the cocycle identity `lineRadical_mul` is stated for. -/
def lineRadical (n : ℕ) (_χ : RankOneCharacter) (p : lineParabolic ℝ) :
    Binary.HomogeneousPoly (n + 1) →ₗ[ℂ] HomogeneousPoly n where
  toFun := lineRadAt n p
  map_add' Q₁ Q₂ := by
    apply Subtype.ext
    simp only [Submodule.coe_add, coe_lineRadAt, lrVecDeriv_add, map_add]
  map_smul' c Q := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, coe_lineRadAt, lrVecDeriv_smul, map_smul, RingHom.id_apply]

theorem coe_lineRadical (n : ℕ) (χ : RankOneCharacter) (p : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    (lineRadical n χ p Q : Poly) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (lrVecDeriv (algebraMap ℝ ℂ (lrC0 p)) (algebraMap ℝ ℂ (lrC1 p)) (Q : Binary.Poly)) := rfl

/-! ## The Levi action `⋆` on binary forms -/

/-- The scalar `p ↦ χ(p) · d_p⁻² · det A_p` as a homomorphism. -/
def lineCharHom (χ : RankOneCharacter) : lineParabolic ℝ →* ℂ :=
  (componentCharacter χ).comp (lineParabolic ℝ).subtype

/-- The homomorphism `p ↦ d_p⁻¹ ∈ ℂ` (`d_p` the corner entry). -/
def lrCornerInvHom : lineParabolic ℝ →* ℂ where
  toFun p := algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹)
  map_one' := by
    have h : (1 : lineParabolic ℝ).1.val 0 0 = 1 := rfl
    show algebraMap ℝ ℂ (((1 : lineParabolic ℝ).1.val 0 0)⁻¹) = 1
    rw [h, _root_.inv_one, map_one]
  map_mul' p q := by
    show algebraMap ℝ ℂ (((p * q).1.val 0 0)⁻¹) =
      algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹) * algebraMap ℝ ℂ ((q.1.val 0 0)⁻¹)
    rw [lr_mul_e00, _root_.mul_inv, map_mul]

/-- The determinant of the lower block `A_p`, complexified, as a homomorphism. -/
def lineDetHom : lineParabolic ℝ →* ℂ :=
  (Units.coeHom ℂ).comp
    ((GeneralLinearGroup.det : GeneralLinearGroup (Fin 2) ℂ →* ℂˣ).comp
      ((GeneralLinearGroup.map (algebraMap ℝ ℂ) :
          GeneralLinearGroup (Fin 2) ℝ →* GeneralLinearGroup (Fin 2) ℂ).comp lineLeviBlockHom))

/-- The scalar `θ(p) = χ(p) · d_p⁻² · det A_p` by which `⋆` differs from the standard action. -/
def lineTheta (χ : RankOneCharacter) : lineParabolic ℝ →* ℂ :=
  lineCharHom χ * (lrCornerInvHom * lrCornerInvHom) * lineDetHom

theorem lineTheta_apply (χ : RankOneCharacter) (p : lineParabolic ℝ) :
    lineTheta χ p =
      componentCharacter χ p.1 *
          (algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹) * algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹)) *
        ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) :
          ℂˣ) : ℂ) := rfl

/-- **The action `⋆` of the real line parabolic on binary forms of degree `k`**:
`(p ⋆ Q)(y) = χ(p) d_p⁻² Q(A_p⁻¹ y)`. -/
def lineStar (χ : RankOneCharacter) (k : ℕ) :
    Representation ℂ (lineParabolic ℝ) (Binary.HomogeneousPoly k) where
  toFun p := lineTheta χ p •
    Binary.homogeneousAction k (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p))
  map_one' := by
    have h : lineLeviBlock (1 : lineParabolic ℝ) = 1 := lineLeviBlockHom.map_one
    simp [h]
  map_mul' p q := by
    have h : lineLeviBlock (p * q) = lineLeviBlock p * lineLeviBlock q :=
      lineLeviBlockHom.map_mul p q
    apply LinearMap.ext
    intro v
    change lineTheta χ (p * q) •
        Binary.homogeneousAction k (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock (p * q))) v =
      lineTheta χ p •
        Binary.homogeneousAction k (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p))
          (lineTheta χ q •
            Binary.homogeneousAction k (-1)
              (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock q)) v)
    simp only [h, map_mul, Module.End.mul_apply, map_smul, smul_smul]

theorem lineStar_apply (χ : RankOneCharacter) (k : ℕ) (p : lineParabolic ℝ) :
    lineStar χ k p =
      lineTheta χ p •
        Binary.homogeneousAction k (-1)
          (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) := rfl

/-- The block of a line Levi element is its `GL₂` factor. -/
theorem lineLeviBlock_levi (d : ℝˣ) (A : GeneralLinearGroup (Fin 2) ℝ) :
    lineLeviBlock ⟨lineLevi d A, lineLevi_mem d A⟩ = A := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lineLeviBlock, lrBlockP, lrLowerBlock, lineLevi_val]

/-- The corner of a line Levi element is its `GL₁` factor. -/
theorem lr_corner_levi (d : ℝˣ) (A : GeneralLinearGroup (Fin 2) ℝ) :
    (lineLevi d A).val 0 0 = (d : ℝ) := by
  simp [lineLevi_val]

theorem lineStar_mul_apply (χ : RankOneCharacter) (k : ℕ) (p q : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    lineStar χ k (p * q) Q = lineStar χ k p (lineStar χ k q Q) := by
  rw [map_mul, Module.End.mul_apply]

theorem lineStar_one_apply (χ : RankOneCharacter) (k : ℕ) (Q : Binary.HomogeneousPoly k) :
    lineStar χ k 1 Q = Q := by
  rw [map_one, Module.End.one_apply]

theorem lineStar_inv_cancel (χ : RankOneCharacter) (k : ℕ) (p : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) : lineStar χ k p (lineStar χ k p⁻¹ Q) = Q := by
  rw [← lineStar_mul_apply, mul_inv_cancel, lineStar_one_apply]

theorem coe_lineStar (χ : RankOneCharacter) (k : ℕ) (p : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    ((lineStar χ k p Q : Binary.HomogeneousPoly k) : Binary.Poly) =
      lineTheta χ p •
        Binary.action (-1) (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p))
          (Q : Binary.Poly) := rfl

/-- The complexified lower block of the inverse of `p`. -/
def lineInvBlockC (p : lineParabolic ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j => algebraMap ℝ ℂ (p.1.inv i.succ j.succ)

theorem lineInvBlockC_00 (p : lineParabolic ℝ) :
    lineInvBlockC p 0 0 = algebraMap ℝ ℂ (p.1.inv 1 1) := rfl

theorem lineInvBlockC_01 (p : lineParabolic ℝ) :
    lineInvBlockC p 0 1 = algebraMap ℝ ℂ (p.1.inv 1 2) := rfl

theorem lineInvBlockC_10 (p : lineParabolic ℝ) :
    lineInvBlockC p 1 0 = algebraMap ℝ ℂ (p.1.inv 2 1) := rfl

theorem lineInvBlockC_11 (p : lineParabolic ℝ) :
    lineInvBlockC p 1 1 = algebraMap ℝ ℂ (p.1.inv 2 2) := rfl

theorem lr_star_inv_block (p : lineParabolic ℝ) :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)).inv :
        Matrix (Fin 2) (Fin 2) ℂ) = lineInvBlockC p := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- `p ⋆ Q = χ(p) d_p⁻² · Q ∘ A_p⁻¹` on the level of polynomials. -/
theorem coe_lineStar_substitute (χ : RankOneCharacter) (k : ℕ) (p : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly k) :
    ((lineStar χ k p Q : Binary.HomogeneousPoly k) : Binary.Poly) =
      (componentCharacter χ p.1 *
          (algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹) * algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹))) •
        Binary.substitute (lineInvBlockC p) (Q : Binary.Poly) := by
  have hD : ((GeneralLinearGroup.det (GeneralLinearGroup.map (algebraMap ℝ ℂ) (lineLeviBlock p)) :
      ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  rw [coe_lineStar, binary_action_neg_one, smul_smul, lineTheta_apply,
    mul_inv_cancel_right₀ hD, lr_star_inv_block]

/-! ## The coefficient representation on forms free of `x₀` -/

theorem lr_mapInv_succ_zero {g : RealGL3} (hg : InLineParabolic g) (i : Fin 2) :
    ((GeneralLinearGroup.map (algebraMap ℝ ℂ) g)⁻¹ : GL3).val i.succ 0 = 0 := by
  have h := inLine_inv hg
  fin_cases i
  · exact (congrArg (algebraMap ℝ ℂ) h.1).trans (map_zero _)
  · exact (congrArg (algebraMap ℝ ℂ) h.2).trans (map_zero _)

/-- The coefficient representation acts on `x₀`-free forms through the lower block of the
inverse. -/
theorem lr_fullCoefficient_rename_succ (χ : RankOneCharacter) (p : lineParabolic ℝ)
    (G : Binary.Poly) :
    fullCoefficientComponent χ p.1 (rename (Fin.succ : Fin 2 → Fin 3) G) =
      (componentCharacter χ p.1 * (algebraMap ℝ ℂ (p.1.val 0 0 * lrDet p))⁻¹) •
        rename (Fin.succ : Fin 2 → Fin 3) (Binary.substitute (lineInvBlockC p) G) := by
  have hp : InLineParabolic p.1 := p.2
  rw [fullCoefficientComponent_apply,
    lr_substitute_rename_succ (N := ((GeneralLinearGroup.map (algebraMap ℝ ℂ) p.1)⁻¹ : GL3))
      (lr_mapInv_succ_zero hp),
    lr_det3_map p]
  rfl

/-! ## The cocycle identity -/

/-- The inverse-free form of the cocycle identity. -/
theorem lineRadical_key (n : ℕ) (χ : RankOneCharacter) (p q : lineParabolic ℝ)
    (R : Binary.HomogeneousPoly (n + 1)) :
    ((realCoefficientComponent n χ p.1 (lineRadical n χ q R) : HomogeneousPoly n) : Poly) =
      ((lineRadical n χ (p * q) (lineStar χ (n + 1) p R) : HomogeneousPoly n) : Poly) -
        ((lineRadical n χ p (lineStar χ (n + 1) p R) : HomogeneousPoly n) : Poly) := by
  have hp : InLineParabolic p.1 := p.2
  have hd : p.1.val 0 0 ≠ 0 := lr_corner_ne_zero hp
  have hδ : lrDet p ≠ 0 := lrDet_ne_zero p
  obtain ⟨hΔ0, hΔ1⟩ := lrC_mul p q
  obtain ⟨hB00, hB01, hB10, hB11⟩ := lr_inv_block hp
  have hr0 : p.1.inv 1 1 * (lrC0 (p * q) - lrC0 p) + p.1.inv 1 2 * (lrC1 (p * q) - lrC1 p) =
      p.1.val 0 0 / lrDet p * lrC0 q := by
    rw [hΔ0, hΔ1]
    linear_combination (p.1.val 0 0 / lrDet p * lrC0 q) * hB00 +
      (p.1.val 0 0 / lrDet p * lrC1 q) * hB01
  have hr1 : p.1.inv 2 1 * (lrC0 (p * q) - lrC0 p) + p.1.inv 2 2 * (lrC1 (p * q) - lrC1 p) =
      p.1.val 0 0 / lrDet p * lrC1 q := by
    rw [hΔ0, hΔ1]
    linear_combination (p.1.val 0 0 / lrDet p * lrC0 q) * hB10 +
      (p.1.val 0 0 / lrDet p * lrC1 q) * hB11
  have ha : lineInvBlockC p 0 0 * (algebraMap ℝ ℂ (lrC0 (p * q)) - algebraMap ℝ ℂ (lrC0 p)) +
      lineInvBlockC p 0 1 * (algebraMap ℝ ℂ (lrC1 (p * q)) - algebraMap ℝ ℂ (lrC1 p)) =
      algebraMap ℝ ℂ (p.1.val 0 0 / lrDet p * lrC0 q) := by
    rw [lineInvBlockC_00, lineInvBlockC_01, ← hr0, map_add, map_mul, map_mul, map_sub, map_sub]
  have hb : lineInvBlockC p 1 0 * (algebraMap ℝ ℂ (lrC0 (p * q)) - algebraMap ℝ ℂ (lrC0 p)) +
      lineInvBlockC p 1 1 * (algebraMap ℝ ℂ (lrC1 (p * q)) - algebraMap ℝ ℂ (lrC1 p)) =
      algebraMap ℝ ℂ (p.1.val 0 0 / lrDet p * lrC1 q) := by
    rw [lineInvBlockC_10, lineInvBlockC_11, ← hr1, map_add, map_mul, map_mul, map_sub, map_sub]
  have hs : ∀ c : ℝ,
      (componentCharacter χ p.1 *
          (algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹) * algebraMap ℝ ℂ ((p.1.val 0 0)⁻¹))) *
        algebraMap ℝ ℂ (p.1.val 0 0 / lrDet p * c) =
      (componentCharacter χ p.1 * (algebraMap ℝ ℂ (p.1.val 0 0 * lrDet p))⁻¹) *
        algebraMap ℝ ℂ c := by
    intro c
    have hD : algebraMap ℝ ℂ (p.1.val 0 0) ≠ 0 := rc_algebraMap_ne_zero hd
    have hE : algebraMap ℝ ℂ (lrDet p) ≠ 0 := rc_algebraMap_ne_zero hδ
    simp only [map_mul, map_div₀, map_inv₀]
    field_simp
  simp only [coe_realCoefficientComponent, coe_lineRadical]
  rw [lr_fullCoefficient_rename_succ, coe_lineStar_substitute, lr_rename_vecDeriv_sub,
    lrVecDeriv_smul, lrVecDeriv_substitute, map_smul, ha, hb,
    lr_smul_rename_substitute_vecDeriv, lr_smul_rename_substitute_vecDeriv, hs, hs]

theorem lineRadical_mul (n : ℕ) (χ : RankOneCharacter) (p₁ p₂ : lineParabolic ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    lineRadical n χ (p₁ * p₂) Q =
      lineRadical n χ p₁ Q +
        realCoefficientComponent n χ p₁.1
          (lineRadical n χ p₂ (lineStar χ (n + 1) p₁⁻¹ Q)) := by
  have hK := lineRadical_key n χ p₁ p₂ (lineStar χ (n + 1) p₁⁻¹ Q)
  rw [lineStar_inv_cancel] at hK
  apply Subtype.ext
  rw [Submodule.coe_add, hK]
  ring

/-! ## Vanishing on the Levi subgroup -/

theorem lineRadical_eq_zero_of_row_zero (n : ℕ) (χ : RankOneCharacter) (p : lineParabolic ℝ)
    (h1 : p.1.val 0 1 = 0) (h2 : p.1.val 0 2 = 0) : lineRadical n χ p = 0 := by
  obtain ⟨h01, h02⟩ := lrC_of_zero p h1 h2
  apply LinearMap.ext
  intro Q
  apply Subtype.ext
  rw [coe_lineRadical, h01, h02]
  simp [lrVecDeriv]

/-- The radical vanishes on the Levi subgroup. -/
theorem lineRadical_levi_eq_zero (n : ℕ) (χ : RankOneCharacter) (d : ℝˣ)
    (A : GeneralLinearGroup (Fin 2) ℝ) :
    lineRadical n χ ⟨lineLevi d A, lineLevi_mem d A⟩ = 0 := by
  apply lineRadical_eq_zero_of_row_zero
  · show (lineLevi d A).val 0 1 = 0
    simp [lineLevi_val]
  · show (lineLevi d A).val 0 2 = 0
    simp [lineLevi_val]

/-- The radical is invariant under right multiplication by the Levi subgroup. -/
theorem lineRadical_mul_levi (n : ℕ) (χ : RankOneCharacter) (p : lineParabolic ℝ) (d : ℝˣ)
    (A : GeneralLinearGroup (Fin 2) ℝ) :
    lineRadical n χ (p * ⟨lineLevi d A, lineLevi_mem d A⟩) = lineRadical n χ p := by
  apply LinearMap.ext
  intro Q
  rw [lineRadical_mul, lineRadical_levi_eq_zero]
  simp

/-- Left multiplication by a Levi element conjugates the radical. -/
theorem lineRadical_levi_mul (n : ℕ) (χ : RankOneCharacter) (d : ℝˣ)
    (A : GeneralLinearGroup (Fin 2) ℝ) (p : lineParabolic ℝ) (Q : Binary.HomogeneousPoly (n + 1)) :
    lineRadical n χ (⟨lineLevi d A, lineLevi_mem d A⟩ * p) Q =
      realCoefficientComponent n χ (lineLevi d A)
        (lineRadical n χ p (lineStar χ (n + 1) ⟨lineLevi d A, lineLevi_mem d A⟩⁻¹ Q)) := by
  rw [lineRadical_mul, lineRadical_levi_eq_zero]
  simp

/-! ## The explicit formula on the radical -/

theorem lr_lineUnipotent_mem (s t : ℝ) : lineUnipotent s t ∈ lineParabolic ℝ := ⟨rfl, rfl⟩

theorem lrC0_unipotent (s t : ℝ) : lrC0 ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩ = t := by
  have e11 : (lineUnipotent s t).val 1 1 = 1 := rfl
  have e12 : (lineUnipotent s t).val 1 2 = 0 := rfl
  have e21 : (lineUnipotent s t).val 2 1 = 0 := rfl
  have e22 : (lineUnipotent s t).val 2 2 = 1 := rfl
  have e01 : (lineUnipotent s t).val 0 1 = s := rfl
  have e02 : (lineUnipotent s t).val 0 2 = t := rfl
  unfold lrC0 lrDet
  show ((lineUnipotent s t).val 1 1 * (lineUnipotent s t).val 0 2 -
      (lineUnipotent s t).val 1 2 * (lineUnipotent s t).val 0 1) /
    ((lineUnipotent s t).val 1 1 * (lineUnipotent s t).val 2 2 -
      (lineUnipotent s t).val 1 2 * (lineUnipotent s t).val 2 1) = t
  rw [e11, e12, e21, e22, e01, e02]
  simp

theorem lrC1_unipotent (s t : ℝ) : lrC1 ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩ = -s := by
  have e11 : (lineUnipotent s t).val 1 1 = 1 := rfl
  have e12 : (lineUnipotent s t).val 1 2 = 0 := rfl
  have e21 : (lineUnipotent s t).val 2 1 = 0 := rfl
  have e22 : (lineUnipotent s t).val 2 2 = 1 := rfl
  have e01 : (lineUnipotent s t).val 0 1 = s := rfl
  have e02 : (lineUnipotent s t).val 0 2 = t := rfl
  unfold lrC1 lrDet
  show ((lineUnipotent s t).val 2 1 * (lineUnipotent s t).val 0 2 -
      (lineUnipotent s t).val 2 2 * (lineUnipotent s t).val 0 1) /
    ((lineUnipotent s t).val 1 1 * (lineUnipotent s t).val 2 2 -
      (lineUnipotent s t).val 1 2 * (lineUnipotent s t).val 2 1) = -s
  rw [e11, e12, e21, e22, e01, e02]
  simp

/-- **The explicit formula on the radical**: for `u = lineUnipotent s t`,
`R(u) Q = ι (t ∂₀ Q - s ∂₁ Q)` (derivatives of the binary form `Q`). -/
theorem coe_lineRadical_unipotent (n : ℕ) (χ : RankOneCharacter) (s t : ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    ((lineRadical n χ ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩ Q : HomogeneousPoly n) :
        Poly) =
      rename (Fin.succ : Fin 2 → Fin 3)
        (C (algebraMap ℝ ℂ t) * pderiv (0 : Fin 2) (Q : Binary.Poly) -
          C (algebraMap ℝ ℂ s) * pderiv (1 : Fin 2) (Q : Binary.Poly)) := by
  rw [coe_lineRadical, lrC0_unipotent, lrC1_unipotent]
  simp only [lrVecDeriv, map_neg, map_sub, map_add, map_mul, rename_C]
  ring

/-- The explicit formula on the radical, in the ternary variables:
`R(u) Q = t ∂_{x₁} (ι Q) - s ∂_{x₂} (ι Q)`. -/
theorem coe_lineRadical_unipotent_three (n : ℕ) (χ : RankOneCharacter) (s t : ℝ)
    (Q : Binary.HomogeneousPoly (n + 1)) :
    ((lineRadical n χ ⟨lineUnipotent s t, lr_lineUnipotent_mem s t⟩ Q : HomogeneousPoly n) :
        Poly) =
      C (algebraMap ℝ ℂ t) * pderiv (1 : Fin 3) (lineEmbed (n + 1) Q) -
        C (algebraMap ℝ ℂ s) * pderiv (2 : Fin 3) (lineEmbed (n + 1) Q) := by
  have h0 : pderiv (1 : Fin 3) (rename (Fin.succ : Fin 2 → Fin 3) (Q : Binary.Poly)) =
      rename (Fin.succ : Fin 2 → Fin 3) (pderiv (0 : Fin 2) (Q : Binary.Poly)) :=
    pderiv_rename (Fin.succ_injective 2) 0 _
  have h1 : pderiv (2 : Fin 3) (rename (Fin.succ : Fin 2 → Fin 3) (Q : Binary.Poly)) =
      rename (Fin.succ : Fin 2 → Fin 3) (pderiv (1 : Fin 2) (Q : Binary.Poly)) :=
    pderiv_rename (Fin.succ_injective 2) 1 _
  rw [coe_lineRadical_unipotent, lineEmbed_apply, h0, h1]
  simp only [map_sub, map_mul, rename_C]

end TernaryPeriodPolynomials.SourceConstruction

end
