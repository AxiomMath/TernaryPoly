module

public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.BadLineCuspsWiring
public import TernaryPeriodPolynomials.ArithmeticCohomology.FiberModel.JFClass

@[expose] public section


/-!
# The model's `a_F`-radical coordinate is the positive cocycle on `Γ₂` (outside the bridge fields)

Paper: (`lem:bad-line-coordinate`: "its cocycle is the negative of the one whose specified order-three
generator has value `J_f`") and 1676.  The library's `PolynomialBoundaryBridge` records the
generator values `mixedBernoulliCoordinate c binaryA = -J_f`, `binaryB ↦ 0`, `binaryR ↦ 0` as
fields.  Here the whole function `g ↦ -𝒥(mixed bar edge of z_F at diag(1,g))` on
`Γ₂ ⊂ GL₂(ℤ)` (the Levi embedding `iota`, `diag(1, g) ∈ K†` for `g ∈ Γ₂`) is shown to be a
cocycle for the coefficient action on binary forms (`modelCocycle_isCocycle`), by induction over
the generators `A₀, B₀, R₀` from the left-generator product formula
`mixedBernoulliCoordinate_generator_product`, i.e. a `PositiveCocycle` (`modelCocycle_positive`), and
the paper's cusp and detection arguments (`BadLineCusps`, `JFClass`) are applied to it
(`prop_4_2_bad_line_literal`).  Also `zF_literal`: the library's `pathCocycle` is, at `(1,g,gh)`, the
paper's `z_F(g,h) = F(τ(g) + gτ(h) - τ(gh))`; its cocycle property
(`pathCochain_cocycle`), path-independence of the class (`realizesPathClass_class_independent`) and
vanishing on good-vertex stabilizers (`pathCocycle_goodBoundaryVanishing`) are library theorems.

Formalized by Claude Sonnet 5.5.
-/

open MvPolynomial GeneralEisenstein Matrix
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.Argument.FiberModel
open TernaryPeriodPolynomials.Argument.FiberModel.BadLineCusps

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel.ModelCocycle

/-- The Levi embedding `g ↦ diag(1, g)` of `GL₂(ℤ)` into `GL₃(ℤ)`. -/
def embed3 (g : GL2Z) : IntegralGL3 where
  val := !![1, 0, 0; 0, g.val 0 0, g.val 0 1; 0, g.val 1 0, g.val 1 1]
  inv := !![1, 0, 0; 0, (g⁻¹ : GL2Z).val 0 0, (g⁻¹ : GL2Z).val 0 1;
    0, (g⁻¹ : GL2Z).val 1 0, (g⁻¹ : GL2Z).val 1 1]
  val_inv := by
    have h := g.val_inv
    have e : ∀ i j, (g.val * (g⁻¹ : GL2Z).val) i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j => by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]
  inv_val := by
    have e : ∀ i j, ((g⁻¹ : GL2Z).val * g.val) i j = (1 : Matrix (Fin 2) (Fin 2) ℤ) i j :=
      fun i j => by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e00 := e 0 0; have e01 := e 0 1; have e10 := e 1 0; have e11 := e 1 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, e00, e01, e10, e11]

theorem embed3_val (g : GL2Z) :
    (embed3 g).val = !![1, 0, 0; 0, g.val 0 0, g.val 0 1; 0, g.val 1 0, g.val 1 1] := rfl

theorem embed3_one : embed3 1 = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [embed3_val]

theorem embed3_mul (g h : GL2Z) : embed3 (g * h) = embed3 g * embed3 h := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embed3_val, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two]

theorem embed3_mem {g : GL2Z} (hg : g ∈ Gamma2) : embed3 g ∈ arithmeticLevel := by
  rw [mem_Gamma2] at hg
  change lastRow ᵥ* (reductionThree (embed3 g)).val = lastRow
  simp only [lastRow, Matrix.single_vecMul, one_smul]
  ext index
  fin_cases index
  · rfl
  · change ((g.val 1 0 : ℤ) : ZMod 3) = 0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by omega)
  · change ((g.val 1 1 : ℤ) : ZMod 3) = 1
    have := ZMod.intCast_eq_intCast_iff' (g.val 1 1) 1 3
    simp only [Int.cast_one] at this
    rw [this]; omega

/-- The Levi embedding `Γ₂ → K†` (`g ↦ diag(1,g)`). -/
def iota : Gamma2G →* rationalLevel where
  toFun g := integralImage (embed3 g.1) (embed3_mem g.2)
  map_one' := by
    apply Subtype.ext
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (embed3 1) = 1
    rw [embed3_one, map_one]
  map_mul' g h := by
    apply Subtype.ext
    change GeneralLinearGroup.map (Int.castRingHom ℚ) (embed3 (g.1 * h.1)) =
      GeneralLinearGroup.map (Int.castRingHom ℚ) (embed3 g.1) *
        GeneralLinearGroup.map (Int.castRingHom ℚ) (embed3 h.1)
    rw [embed3_mul, map_mul]

theorem iota_val (g : Gamma2G) :
    (iota g).val = GeneralLinearGroup.map (Int.castRingHom ℚ) (embed3 g.1) := rfl

theorem iota_entries (g : Gamma2G) (i j : Fin 3) :
    ((iota g).val.val i j : ℚ) = (((embed3 g.1).val i j : ℤ) : ℚ) := rfl

theorem iota_a0 : iota a0 = arithmeticBinaryA := by
  apply Subtype.ext
  rw [arithmeticBinaryA_val]
  apply Units.ext
  ext i j
  rw [iota_entries]
  fin_cases i <;> fin_cases j <;> simp [embed3_val, a0, A0, binaryA]

theorem iota_b0 : iota b0 = arithmeticBinaryB := by
  apply Subtype.ext
  rw [arithmeticBinaryB_val]
  apply Units.ext
  ext i j
  rw [iota_entries]
  fin_cases i <;> fin_cases j <;> simp [embed3_val, b0, B0, binaryB]

theorem iota_r0 : iota r0 = arithmeticBinaryR := by
  apply Subtype.ext
  rw [arithmeticBinaryR_val]
  apply Units.ext
  ext i j
  rw [iota_entries]
  fin_cases i <;> fin_cases j <;> simp [embed3_val, r0, R0, binaryR]

theorem iota_line (g : Gamma2G) : (iota g).val ∈ Adelic.lineParabolic ℚ := by
  refine ⟨?_, ?_⟩ <;> rw [iota_entries] <;> simp [embed3_val]

theorem iota_block (g : Gamma2G) : (iota g).val.val 0 1 = 0 ∧ (iota g).val.val 0 2 = 0 := by
  constructor <;> rw [iota_entries] <;> simp [embed3_val]

section Model

open BadLineCuspsWiring Homogeneous

/-- **The literal radical coordinate of the model's `a_F`-cocycle on `Γ₂`**:
`c(g) = -𝒥(mixed edge of z_F at diag(1,g))`, in the binary coordinates `(Y,Z)`: the negative of the
Bernoulli coordinate of the mixed bar edge, so that its value at `A₀` is `J_f` (lemma
`bad-line-coordinate`: "its cocycle is the negative of the one whose specified order-three
generator has value `J_f`"). -/
def modelCocycle {degree : ℕ}
    (cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter))
    (g : Gamma2G) : MvPolynomial (Fin 2) ℂ :=
  -toBinary (mixedBernoulliCoordinate cocycle (iota g).val)

variable {degree : ℕ} (degree_positive : 0 < degree) {polynomial : HomogeneousPoly degree}
  {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
  (functional_property : IsPolynomialFunctional polynomial functional)
  {cocycle : cocycles rationalLevel (rationalCoefficientComponent degree trivialCharacter)}
  (realizes : RealizesPathClass functional specialPaths cocycle)

include degree_positive functional_property realizes

theorem modelCocycle_left_a0 (h : Gamma2G) :
    modelCocycle cocycle (a0 * h) =
      modelCocycle cocycle a0 + repG ℂ a0 (modelCocycle cocycle h) := by
  have key := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (iota h) (iota_line h) (iota_block h)).1
  unfold modelCocycle
  rw [_root_.map_mul, iota_a0, key, arithmeticBinaryA_val]
  have e : toBinary ((bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2])
      (mixedBernoulliCoordinate cocycle (iota h).val)) =
      repG ℂ a0 (toBinary (mixedBernoulliCoordinate cocycle (iota h).val)) :=
    toBinary_A (mixedBernoulliCoordinate cocycle (iota h).val)
  rw [_root_.map_add, e, _root_.map_neg]
  abel

theorem modelCocycle_left_b0 (h : Gamma2G) :
    modelCocycle cocycle (b0 * h) =
      modelCocycle cocycle b0 + repG ℂ b0 (modelCocycle cocycle h) := by
  have key := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (iota h) (iota_line h) (iota_block h)).2.1
  unfold modelCocycle
  rw [_root_.map_mul, iota_b0, key, arithmeticBinaryB_val]
  have e : toBinary ((bind₁ ![X 0, -X 1, -3 * X 1 + X 2])
      (mixedBernoulliCoordinate cocycle (iota h).val)) =
      repG ℂ b0 (toBinary (mixedBernoulliCoordinate cocycle (iota h).val)) :=
    toBinary_B (mixedBernoulliCoordinate cocycle (iota h).val)
  rw [_root_.map_add, e, _root_.map_neg]
  abel

theorem modelCocycle_left_r0 (h : Gamma2G) :
    modelCocycle cocycle (r0 * h) =
      modelCocycle cocycle r0 + repG ℂ r0 (modelCocycle cocycle h) := by
  have key := (mixedBernoulliCoordinate_generator_product degree_positive functional_property
    realizes (iota h) (iota_line h) (iota_block h)).2.2
  unfold modelCocycle
  rw [_root_.map_mul, iota_r0, key, arithmeticBinaryR_val]
  have e : toBinary ((bind₁ ![X 0, -X 1, X 2])
      (mixedBernoulliCoordinate cocycle (iota h).val)) =
      repG ℂ r0 (toBinary (mixedBernoulliCoordinate cocycle (iota h).val)) :=
    toBinary_R (mixedBernoulliCoordinate cocycle (iota h).val)
  rw [_root_.map_add, e, _root_.map_neg]
  abel

omit degree_positive functional_property in
theorem modelCocycle_one : modelCocycle cocycle 1 = 0 := by
  unfold modelCocycle
  rw [_root_.map_one, Subgroup.coe_one, mixedBernoulliCoordinate_one realizes, _root_.map_zero,
    neg_zero]

/-- **The model's mixed Bernoulli coordinate is a cocycle on `Γ₂`** for the coefficient action on
binary forms (all of `Γ₂`, not only the generators): induction on the word length in the generators
`A₀, B₀, R₀`, from the left-generator product formula
`mixedBernoulliCoordinate_generator_product`. -/
theorem modelCocycle_isCocycle : IsCocycle (repG ℂ) (modelCocycle cocycle) := by
  have hQ : ∀ g ∈ Subgroup.closure ({a0, b0, r0} : Set Gamma2G), ∀ h,
      modelCocycle cocycle (g * h) = modelCocycle cocycle g + repG ℂ g (modelCocycle cocycle h) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl | rfl
      · exact modelCocycle_left_a0 degree_positive functional_property realizes
      · exact modelCocycle_left_b0 degree_positive functional_property realizes
      · exact modelCocycle_left_r0 degree_positive functional_property realizes
    | one =>
      intro h
      rw [one_mul, modelCocycle_one realizes, zero_add,
        _root_.map_one]
      rfl
    | mul x y _ _ hx hy =>
      intro h
      rw [mul_assoc, hx (y * h), hy h, hx y]
      simp only [_root_.map_add, _root_.map_mul, Module.End.mul_apply]
      abel
    | inv x _ hx =>
      intro h
      have h1 := hx (x⁻¹ * h)
      rw [mul_inv_cancel_left] at h1
      have h0 := hx x⁻¹
      rw [mul_inv_cancel, modelCocycle_one realizes] at h0
      have hinv : modelCocycle cocycle x⁻¹ = -(repG ℂ x⁻¹ (modelCocycle cocycle x)) := by
        have := congrArg (repG ℂ x⁻¹) h0.symm
        rw [_root_.map_add, ← Module.End.mul_apply, ← _root_.map_mul, inv_mul_cancel,
          _root_.map_one, Module.End.one_apply, _root_.map_zero] at this
        exact eq_neg_of_add_eq_zero_right this
      have := congrArg (repG ℂ x⁻¹) h1
      rw [_root_.map_add, ← Module.End.mul_apply, ← _root_.map_mul, inv_mul_cancel,
        _root_.map_one, Module.End.one_apply] at this
      rw [hinv, this]
      abel
  intro g h
  exact hQ g (by rw [closure_a0_b0_r0]; trivial) h

theorem modelCocycle_positive :
    PositiveCocycle ℂ (degree + 1) (modelCocycle cocycle) := by
  refine ⟨modelCocycle_isCocycle degree_positive functional_property realizes, ?_, ?_, ?_⟩
  · unfold modelCocycle
    rw [iota_b0, arithmeticBinaryB_val, mixedBernoulliCoordinate_binaryB realizes]
    simp
  · unfold modelCocycle
    rw [iota_r0, arithmeticBinaryR_val, mixedBernoulliCoordinate_binaryR realizes]
    simp
  · unfold modelCocycle
    rw [iota_a0, arithmeticBinaryA_val, mixedBernoulliCoordinate_binaryA functional_property realizes]
    simp only [_root_.map_neg, neg_neg]
    exact toBinary_homog (bernoulliObstruction_homogeneous polynomial)

omit degree_positive in
theorem modelCocycle_a0 :
    modelCocycle cocycle a0 = toBinary (bernoulliObstruction polynomial) := by
  unfold modelCocycle
  rw [iota_a0, arithmeticBinaryA_val, mixedBernoulliCoordinate_binaryA functional_property realizes]
  simp

end Model

open SymBoundaryFactors BadLineCuspsWiring in
/-- **Proposition 4.2, the bad-line step, literally**.  For a symmetric solution `f`
of positive degree `n`, the model's literal mixed-bar-edge radical coordinate of the connecting
cocycle `z_F` (built from `f` through the path family `specialPaths`) restricts, on the binary Levi
`Γ₂` embedded as `diag(1, g)`, to a positive cocycle `c` of the coefficient action on binary forms
of degree `n + 1`, with `c(A₀) = J_f`, `c(B₀) = c(R₀) = 0` (not only on the generators: it is a
cocycle on all of `Γ₂`).  Then:

* both cusp restrictions of `c` are coboundaries on the cusp stabilizers `⟨U₀,R₀⟩`, `⟨T,R₀⟩`;
* if the class `[u]` vanishes in `V/(V^{⟨A,B⟩} + V^R)` (equivalently `c` is a coboundary on `Γ₂`,
  i.e. `j_F = 0`), then `J_f = 0` as a polynomial. -/
theorem prop_4_2_bad_line_literal (n : ℕ) (hn : 0 < n) (f : HomogeneousPoly n)
    (hf : SymmetricSolution f) :
    ∃ c : Gamma2G → MvPolynomial (Fin 2) ℂ, PositiveCocycle ℂ (n + 1) c ∧
      c a0 = toBinary (bernoulliObstruction f) ∧
      ((∃ m : MvPolynomial (Fin 2) ℂ, ∀ s ∈ cuspStabLower, c s = m - repG ℂ s m) ∧
        (∃ m : MvPolynomial (Fin 2) ℂ, ∀ s ∈ cuspStabUpper, c s = m - repG ℂ s m)) ∧
      ((∃ m : MvPolynomial (Fin 2) ℂ, m.IsHomogeneous (n + 1) ∧ ∀ g, c g = m - repG ℂ g m) →
        toBinary (bernoulliObstruction f) = 0) := by
  have hF := polynomialEdgeFunctional_property hf
  have hreal := pathCocycle_realizes hF specialPaths_isPathFamily
  have hpos := modelCocycle_positive hn hF hreal
  refine ⟨modelCocycle (pathCocycle hF specialPaths_isPathFamily), hpos,
    modelCocycle_a0 hF hreal, ?_, ?_⟩
  · have hodd : Odd (n + 1) → eval ![1, 3] (modelCocycle (pathCocycle hF specialPaths_isPathFamily) a0) = 0 := by
      intro ho
      rw [modelCocycle_a0 hF hreal, eval_toBinary]
      have hev : Even n := by simpa [Nat.odd_add_one, Nat.not_odd_iff_even] using ho
      have := bernoulliObstruction_three_Y hn hev f hf 0 1
      simpa [polynomialValue] using this
    exact hpos.cusp_H1_restrictions_vanish hpos.hom_all hodd
  · intro hm
    have h0 : eval ![0, 1] (modelCocycle (pathCocycle hF specialPaths_isPathFamily) a0) = 0 := by
      rw [modelCocycle_a0 hF hreal, eval_toBinary]
      have := bernoulliObstruction_zero_Y f hf 0 1
      simpa [polynomialValue] using this
    obtain ⟨m, hmh, hmc⟩ := hm
    have := hpos.eq_zero_of_jF_zero (by omega) (hpos.jF_zero_iff.mp ⟨m, hmh, hmc⟩) h0
    rwa [modelCocycle_a0 hF hreal] at this

/-- **The library's `pathCocycle` is the paper's `z_F`** (`eq:zF`):
`z_F(g,h) = F(τ(g) + g τ(h) - τ(gh))`, i.e. the homogeneous cocycle at `(1, g, gh)`. -/
theorem zF_literal {degree : ℕ} {polynomial : HomogeneousPoly degree}
    {functional : EdgeChains →ₗ[ℂ] HomogeneousPoly degree}
    (functional_property : IsPolynomialFunctional polynomial functional)
    {paths : rationalLevel → EdgeChains} (paths_good : IsPathFamily paths)
    (g h : rationalLevel) :
    (pathCocycle functional_property paths_good).val.val ![(1 : rationalLevel).val, g.val, (g * h).val] =
      functional (paths g + translateChain g.val (paths h) - paths (g * h)) := by
  have := pathCocycle_realizes functional_property paths_good 1 g (g * h)
  rw [this]
  simp only [inv_one, one_mul, inv_mul_cancel_left, Subgroup.coe_one]
  rw [_root_.map_one]
  rfl


end TernaryPeriodPolynomials.Argument.FiberModel.ModelCocycle
