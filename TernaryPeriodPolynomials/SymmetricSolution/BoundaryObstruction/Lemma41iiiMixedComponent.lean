module

public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.HochschildSerreRows
public import TernaryPeriodPolynomials.Building.BoundaryApartments.BridgeAssembly

@[expose] public section


/-!
# Lemma 4.1 (iii) with the paper's premise: vanishing of the mixed Hochschild-Serre component forces `J_f = 0`

Formalized by Claude Sonnet 5.5.  And the proof at
("If it is zero, then `J_f = 0` as a polynomial").

For the bad-line stabilizer `H = U ⋊ L` of `K†` (`U = radicalQ`, `L = leviQ`) the mixed Hochschild-Serre term is `H¹(L, H¹(U, E_n))`.  For a bar cocycle `c` with only the mixed component
(`PureMixedBadLine c`) its class is represented by the crossed 1-cocycle `e(l)(u) = z(l, l⁻¹ul) - z(u, l)`, `z(a, b) = c(1, a, ab)`, that is `mixedBarEdge c l u`.

* `MixedComponentZero c`: the class of `l ↦ [e(l)] ∈ H¹(U, E_n)` is zero in `H¹(L, H¹(U, E_n))`, literally: there is a 1-cocycle `φ` of `U` with values in `E_n` such that for every `l ∈ L` the class
  `[e(l)] ∈ H¹(U, E_n)` equals `l·[φ] - [φ]`, i.e. `e(l)(u) = l φ(l⁻¹ul) - φ(u) - (u ε_l - ε_l)` for some `ε_l ∈ E_n` (a `U`-coboundary).
* `bernoulliObstruction_of_mixedComponentZero`: for the bar cocycle with the specified order-three generator coordinates, vanishing of the mixed component implies `bernoulliObstruction f = 0`,
  with exactly the hypotheses of the route except that `(globalCoordinates c).2 = 0` (the full line coordinate in the Shapiro-induced module) is replaced by the vanishing of the mixed component alone.
* `lemma41_iii`: the same for the actual cocycle `a_F` of a polynomial functional with the specified paths.

The proof does not use any primitive on the whole stabilizer: it computes the Bernoulli coordinates of the generators `A₀, B₀, R₀` directly from the crossed cocycle `e`.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.PolynomialBadLineNormalization

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

variable {n : ℕ}

/-- **The mixed component of a bar cocycle vanishes** (the class of the crossed cocycle `l ↦ [e(l)]` in `H¹(L, H¹(U, E_n))` is zero). -/
def MixedComponentZero
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∃ φ : RationalGL3 → HomogeneousPoly n,
    (∀ u ∈ radicalQ, ∀ u' ∈ radicalQ,
      φ (u * u') = rationalCoefficientComponent n trivialCharacter u (φ u') + φ u) ∧
    ∀ l ∈ leviQ, ∃ ε : HomogeneousPoly n, ∀ u ∈ radicalQ,
      mixedBarEdge c l u =
        (rationalCoefficientComponent n trivialCharacter l (φ (l⁻¹ * u * l))).val - (φ u).val -
          ((rationalCoefficientComponent n trivialCharacter u ε).val - ε.val)

/-- Edge data of the generator `levi` in the coordinates `(b₁, b₂)`: both mixed edge values are the normal-form values up to a `U`-coboundary. -/
def RadicalEdgeData
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (levi : badLineSubgroup) (b₁ b₂ : HomogeneousPoly n) (first second third fourth : ℤ) : Prop :=
  ∃ κ : HomogeneousPoly n,
    mixedBarEdge c levi.val (badRadical 1 0).val =
      (rationalCoefficientComponent n trivialCharacter levi.val (first • b₁ + second • b₂) - b₁).val -
        ((rationalCoefficientComponent n trivialCharacter (badRadical 1 0).val κ).val - κ.val) ∧
    mixedBarEdge c levi.val (badRadical 0 1).val =
      (rationalCoefficientComponent n trivialCharacter levi.val (third • b₁ + fourth • b₂) - b₂).val -
        ((rationalCoefficientComponent n trivialCharacter (badRadical 0 1).val κ).val - κ.val)


theorem mixedBC_of_edgeData
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    {levi : badLineSubgroup} {b₁ b₂ : HomogeneousPoly n} {first second third fourth : ℤ}
    (h : RadicalEdgeData c levi b₁ b₂ first second third fourth) :
    mixedBernoulliCoordinate c levi.val =
      radicalContractionMap n
        (rationalCoefficientComponent n trivialCharacter levi.val (first • b₁ + second • b₂) - b₁,
         rationalCoefficientComponent n trivialCharacter levi.val (third • b₁ + fourth • b₂) - b₂) := by
  obtain ⟨κ, h1, h2⟩ := h
  simp only [badRadical_val, Int.cast_one, Int.cast_zero] at h1 h2
  let values : HomogeneousPoly n × HomogeneousPoly n :=
    (rationalCoefficientComponent n trivialCharacter levi.val (first • b₁ + second • b₂) - b₁,
     rationalCoefficientComponent n trivialCharacter levi.val (third • b₁ + fourth • b₂) - b₂)
  let coboundary : HomogeneousPoly n × HomogeneousPoly n :=
    (rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 1 0) κ - κ,
     rationalCoefficientComponent n trivialCharacter (Adelic.lineUnipotent 0 1) κ - κ)
  have value : mixedBernoulliCoordinate c levi.val = radicalContractionMap n (values - coboundary) := by
    rw [mixedBernoulliCoordinate, h1, h2]
    rfl
  rw [value, map_sub, radicalContractionMap_coboundary, sub_zero]

theorem generator_coordinates_of_edgeData
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    {b₁ b₂ : HomogeneousPoly n} (d₁ : pderiv 0 b₁.val = 0) (d₂ : pderiv 0 b₂.val = 0)
    (hA : RadicalEdgeData c badBinaryA b₁ b₂ 1 (-1) 3 (-2))
    (hB : RadicalEdgeData c badBinaryB b₁ b₂ (-1) 0 (-3) 1)
    (hR : RadicalEdgeData c badBinaryR b₁ b₂ (-1) 0 0 1) :
    let binary_coordinate := X 2 * b₁.val - X 1 * b₂.val
    mixedBernoulliCoordinate c binaryA =
        bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] binary_coordinate - binary_coordinate ∧
    mixedBernoulliCoordinate c binaryB =
        bind₁ ![X 0, -X 1, -3 * X 1 + X 2] binary_coordinate - binary_coordinate ∧
    mixedBernoulliCoordinate c binaryR =
        bind₁ ![X 0, -X 1, X 2] binary_coordinate - binary_coordinate := by
  have first_preserved := binaryGenerator_preserves_binary n b₁ d₁
  have second_preserved := binaryGenerator_preserves_binary n b₂ d₂
  have coordinate_A := mixedBC_of_edgeData hA
  have coordinate_B := mixedBC_of_edgeData hB
  have coordinate_R := mixedBC_of_edgeData hR
  rw [badBinaryA_val] at coordinate_A
  rw [badBinaryB_val] at coordinate_B
  rw [badBinaryR_val] at coordinate_R
  have derivative_linear (matrix : RationalGL3) (first second : ℤ)
      (preserves_first : pderiv 0
        (rationalCoefficientComponent n trivialCharacter matrix b₁).val = 0)
      (preserves_second : pderiv 0
        (rationalCoefficientComponent n trivialCharacter matrix b₂).val = 0)
      (subtracted : HomogeneousPoly n) (subtracted_binary : pderiv 0 subtracted.val = 0) :
      pderiv 0 (rationalCoefficientComponent n trivialCharacter matrix
        (first • b₁ + second • b₂) - subtracted).val = 0 := by
    simp only [map_add, map_zsmul, Submodule.coe_sub, Submodule.coe_add,
      homogeneousPoly_coe_zsmul, map_zsmul, preserves_first, preserves_second, subtracted_binary,
      zsmul_zero, add_zero, sub_zero, map_sub]
  constructor
  · rw [coordinate_A, radicalContractionMap_binary]
    · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryA, zsmul_eq_mul]
      ring
    · exact derivative_linear binaryA 1 (-1) first_preserved.1 second_preserved.1 b₁ d₁
    · exact derivative_linear binaryA 3 (-2) first_preserved.1 second_preserved.1 b₂ d₂
  · constructor
    · rw [coordinate_B, radicalContractionMap_binary]
      · simp [map_add, map_zsmul, Submodule.coe_add, rationalCoefficient_binaryB, zsmul_eq_mul]
        ring
      · exact derivative_linear binaryB (-1) 0 first_preserved.2.1 second_preserved.2.1 b₁ d₁
      · exact derivative_linear binaryB (-3) 1 first_preserved.2.1 second_preserved.2.1 b₂ d₂
    · rw [coordinate_R, radicalContractionMap_binary]
      · simp [rationalCoefficient_binaryR]
        ring
      · exact derivative_linear binaryR (-1) 0 first_preserved.2.2 second_preserved.2.2 b₁ d₁
      · exact derivative_linear binaryR 0 1 first_preserved.2.2 second_preserved.2.2 b₂ d₂


section StageA

local notation "ρ" => rationalCoefficientComponent n trivialCharacter

/-- The crossed value of the edge for a Levi element, rewritten through the binary normal form `φ(u(s,t)) = s b₁ + t b₂ + (u q - q)` of the cocycle `φ`:
`e(l)(u) = l·(conjugate normal form) - (normal form) - (u κ - κ)`, with `κ = ε - l q + q` (a different `U`-coboundary). -/
theorem edge_formula_of_normalForm
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    {φ : RationalGL3 → HomogeneousPoly n} {b₁ b₂ q : HomogeneousPoly n}
    (normal : ∀ s t : ℤ, φ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      s • b₁ + t • b₂ + (ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) q - q))
    {l : RationalGL3} {ε : HomogeneousPoly n} {s t s'' t'' : ℤ}
    (hconj : l⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * l = Adelic.lineUnipotent (s'' : ℚ) (t'' : ℚ))
    (hε : mixedBarEdge c l (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      (ρ l (φ (l⁻¹ * Adelic.lineUnipotent (s : ℚ) (t : ℚ) * l))).val -
        (φ (Adelic.lineUnipotent (s : ℚ) (t : ℚ))).val -
        ((ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) ε).val - ε.val)) :
    mixedBarEdge c l (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      (ρ l (s'' • b₁ + t'' • b₂) - (s • b₁ + t • b₂)).val -
        ((ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) (ε - ρ l q + q)).val - (ε - ρ l q + q).val) := by
  rw [hε, hconj]
  have key : ρ l (ρ (Adelic.lineUnipotent (s'' : ℚ) (t'' : ℚ)) q) =
      ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) (ρ l q) := by
    have h : l * Adelic.lineUnipotent (s'' : ℚ) (t'' : ℚ) = Adelic.lineUnipotent (s : ℚ) (t : ℚ) * l := by
      rw [← hconj]; group
    rw [← Module.End.mul_apply, ← map_mul, h, map_mul, Module.End.mul_apply]
  have main : ρ l (φ (Adelic.lineUnipotent (s'' : ℚ) (t'' : ℚ))) - φ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) -
        (ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) ε - ε) =
      (ρ l (s'' • b₁ + t'' • b₂) - (s • b₁ + t • b₂)) -
        (ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) (ε - ρ l q + q) - (ε - ρ l q + q)) := by
    rw [normal s'' t'', normal s t]
    simp only [map_add, map_sub, key]
    abel
  have := congrArg Subtype.val main
  simp only [Submodule.coe_sub] at this ⊢
  exact this


theorem radicalQ_mem (s t : ℤ) : Adelic.lineUnipotent (s : ℚ) (t : ℚ) ∈ radicalQ :=
  (mem_radicalQ _).mpr ⟨s, t, rfl⟩

/-- **The mixed component's vanishing gives binary coordinates and edge data for every Levi element.**  There are `b₁, b₂` independent of `X` (the coordinates of `[φ] ∈ H¹(U, E_n)`)
such that every Levi element `l` has edge data in them, whenever its conjugation action on the two radical generators is given by the integers `(first, second)`, `(third, fourth)`. -/
theorem exists_binary_edgeData
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hn : 0 < n) (hmix : MixedComponentZero c) :
    ∃ b₁ b₂ : HomogeneousPoly n, pderiv 0 b₁.val = 0 ∧ pderiv 0 b₂.val = 0 ∧
      ∀ (levi : badLineSubgroup), levi.val ∈ leviQ → ∀ first second third fourth : ℤ,
        levi⁻¹ * badRadical 1 0 * levi = badRadical first second →
        levi⁻¹ * badRadical 0 1 * levi = badRadical third fourth →
        RadicalEdgeData c levi b₁ b₂ first second third fourth := by
  obtain ⟨φ, hφ, hl⟩ := hmix
  let crossed : ℤ → ℤ → HomogeneousPoly n := fun s t => φ (Adelic.lineUnipotent (s : ℚ) (t : ℚ))
  have relation : ∀ first second third fourth : ℤ,
      crossed (first + third) (second + fourth) =
        ρ (integralRadical first second).val (crossed third fourth) + crossed first second := by
    intro first second third fourth
    have h := hφ _ (radicalQ_mem first second) _ (radicalQ_mem third fourth)
    simp only [crossed, integralRadical_val, Int.cast_add]
    rw [Adelic.lineUnipotent_add]
    exact h
  obtain ⟨b₁, b₂, q, d₁, d₂, normal⟩ := radicalCrossed_binary_normalForm hn crossed relation
  have normal' : ∀ s t : ℤ, φ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) =
      s • b₁ + t • b₂ + (ρ (Adelic.lineUnipotent (s : ℚ) (t : ℚ)) q - q) := by
    intro s t
    have := normal s t
    simpa only [crossed, integralRadical_val] using this
  refine ⟨b₁, b₂, d₁, d₂, ?_⟩
  intro levi hlevi first second third fourth hc1 hc2
  obtain ⟨ε, hε⟩ := hl levi.val hlevi
  have conj1 : (levi.val)⁻¹ * Adelic.lineUnipotent ((1 : ℤ) : ℚ) ((0 : ℤ) : ℚ) * levi.val =
      Adelic.lineUnipotent (first : ℚ) (second : ℚ) := by
    have := congrArg Subtype.val hc1
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, badRadical_val] using this
  have conj2 : (levi.val)⁻¹ * Adelic.lineUnipotent ((0 : ℤ) : ℚ) ((1 : ℤ) : ℚ) * levi.val =
      Adelic.lineUnipotent (third : ℚ) (fourth : ℚ) := by
    have := congrArg Subtype.val hc2
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, badRadical_val] using this
  have e1 := edge_formula_of_normalForm (c := c) normal' (ε := ε) conj1
    (by simpa using hε _ (radicalQ_mem 1 0))
  have e2 := edge_formula_of_normalForm (c := c) normal' (ε := ε) conj2
    (by simpa using hε _ (radicalQ_mem 0 1))
  refine ⟨ε - ρ levi.val q + q, ?_, ?_⟩
  · simp only [badRadical_val]
    simpa using e1
  · simp only [badRadical_val]
    simpa using e2


theorem badBinaryA_mem_leviQ : badBinaryA.val ∈ leviQ := by
  rw [mem_leviQ]
  exact ⟨integralBinaryA, integralBinaryA_levi, by rw [badBinaryA_val]; exact arithmeticBinaryA_val.symm.trans rfl⟩

theorem badBinaryB_mem_leviQ : badBinaryB.val ∈ leviQ := by
  rw [mem_leviQ]
  exact ⟨integralBinaryB, integralBinaryB_levi, by rw [badBinaryB_val]; exact arithmeticBinaryB_val.symm.trans rfl⟩

theorem badBinaryR_mem_leviQ : badBinaryR.val ∈ leviQ := by
  rw [mem_leviQ]
  exact ⟨integralBinaryR, integralBinaryR_levi, by rw [badBinaryR_val]; exact arithmeticBinaryR_val.symm.trans rfl⟩

/-- **Lemma 4.1 (iii), the paper's premise**.  Let `c` be a bar cocycle (representing `a_F`) whose coordinates on the order-three generator `A₀` and on `B₀, R₀` are `-J_f`, `0`, `0`
(the specified paths).  If the mixed Hochschild-Serre component of `c` vanishes (`MixedComponentZero c`, the class in `H¹(L, H¹(U, E_n))`), then `J_f = 0` as a polynomial.

Compared with the `bernoulliObstruction_of_lineClass_zero`: the hypothesis `(globalCoordinates c).2 = 0` (the whole line coordinate in `H²(K†, Fun(Flags_line, E_n))`) is replaced by `MixedComponentZero c`. -/
theorem bernoulliObstruction_of_mixedComponentZero {f : HomogeneousPoly n} (hn : 0 < n)
    (solution : SymmetricSolution f)
    (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (coordinate_A : mixedBernoulliCoordinate c binaryA = -bernoulliObstruction f)
    (coordinate_B : mixedBernoulliCoordinate c binaryB = 0)
    (coordinate_R : mixedBernoulliCoordinate c binaryR = 0)
    (hmix : MixedComponentZero c) : bernoulliObstruction f = 0 := by
  obtain ⟨first_binary, second_binary, first_derivative, second_derivative, hdata⟩ :=
    exists_binary_edgeData hn hmix
  have hA := hdata badBinaryA badBinaryA_mem_leviQ 1 (-1) 3 (-2)
    (by simpa using badBinaryA_conjugate 1 0) (by simpa using badBinaryA_conjugate 0 1)
  have hB := hdata badBinaryB badBinaryB_mem_leviQ (-1) 0 (-3) 1
    (by simpa using badBinaryB_conjugate 1 0) (by simpa using badBinaryB_conjugate 0 1)
  have hR := hdata badBinaryR badBinaryR_mem_leviQ (-1) 0 0 1
    (by simpa using badBinaryR_conjugate 1 0) (by simpa using badBinaryR_conjugate 0 1)
  obtain ⟨first_coordinate, second_coordinate, third_coordinate⟩ :=
    generator_coordinates_of_edgeData first_derivative second_derivative hA hB hR
  let binary_polynomial : Poly := X 2 * first_binary.val - X 1 * second_binary.val
  have homogeneous : binary_polynomial.IsHomogeneous (n + 1) := by
    simpa only [binary_polynomial, Nat.add_comm] using
      ((isHomogeneous_X ℂ 2).mul first_binary.property).sub
        ((isHomogeneous_X ℂ 1).mul second_binary.property)
  let binary_primitive : HomogeneousPoly (n + 1) := ⟨binary_polynomial, homogeneous⟩
  have binary : pderiv 0 binary_polynomial = 0 := by
    simp only [binary_polynomial, map_sub, pderiv_mul,
      pderiv_X_of_ne (by decide : (1 : Fin 3) ≠ 0),
      pderiv_X_of_ne (by decide : (2 : Fin 3) ≠ 0), first_derivative, second_derivative,
      zero_mul, mul_zero, add_zero, sub_zero]
  have invariant_B : bind₁ (![X 0, -X 1, -3 * X 1 + X 2] : Fin 3 → Poly)
      binary_polynomial = binary_polynomial := by
    apply sub_eq_zero.mp
    exact second_coordinate.symm.trans coordinate_B
  have invariant_R : bind₁ (![X 0, -X 1, X 2] : Fin 3 → Poly)
      binary_polynomial = binary_polynomial := by
    apply sub_eq_zero.mp
    exact third_coordinate.symm.trans coordinate_R
  have shear (second third : ℂ) : polynomialValue binary_polynomial 0 second (third + 3 * second) =
      polynomialValue binary_polynomial 0 second third := by
    have reflected := polynomialValue_binaryB_invariant binary_polynomial invariant_B (-second) third
    simp only [neg_neg, mul_neg, sub_neg_eq_add] at reflected
    exact reflected.trans (polynomialValue_binaryR_invariant binary_polynomial invariant_R second third)
  have obstruction_coordinate : bernoulliObstruction f = binary_polynomial -
      bind₁ ![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] binary_polynomial := by
    have equality := first_coordinate.symm.trans coordinate_A
    have negated := congrArg Neg.neg equality
    rw [neg_neg] at negated
    rw [← negated]
    change -(bind₁ (![X 0, -2 * X 1 + X 2, -3 * X 1 + X 2] : Fin 3 → Poly)
      binary_polynomial - binary_polynomial) = _
    abel
  exact binaryDetection_of_primitive (by omega : 0 < n + 1) binary_primitive
    (derivative_zero_eval_binary binary_polynomial binary) shear obstruction_coordinate
    (bernoulliObstruction_goodBoundary solution)

/-- **Lemma 4.1 (iii) for the cocycle `a_F` of a polynomial functional with the specified paths**: if the mixed component of `a_F` is zero then `J_f = 0` as a polynomial. -/
theorem lemma41_iii {f : HomogeneousPoly n} (hn : 0 < n) (solution : SymmetricSolution f)
    {F : EdgeChains →ₗ[ℂ] HomogeneousPoly n} (hF : IsPolynomialFunctional f F)
    (hmix : MixedComponentZero (pathCocycle hF specialPaths_isPathFamily)) :
    bernoulliObstruction f = 0 := by
  have realizes := pathCocycle_realizes hF specialPaths_isPathFamily
  exact bernoulliObstruction_of_mixedComponentZero hn solution _
    (mixedBernoulliCoordinate_binaryA hF realizes) (mixedBernoulliCoordinate_binaryB realizes)
    (mixedBernoulliCoordinate_binaryR realizes) hmix

end StageA

end TernaryPeriodPolynomials.Argument.Identities
