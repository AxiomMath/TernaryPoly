module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.CuspReduction
public import TernaryPeriodPolynomials.ArithmeticCohomology.Spectral.ModularSymDimension
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.IdentityPlaneAmbientEdge

@[expose] public section


/-!
# The identity-plane cusp has no cohomology in even degree

Let `Λ₀ = U ⋊ GL₂(ℤ)` be the stabilizer of the identity plane, `U ≅ ℤ²` its unipotent radical,
and `V = Sym^n ⊗ det⁻¹` with `n > 0` even. Then `H²(Λ₀, V) = 0`.

* **Restriction to `U` vanishes.** A two-cocycle `z` of `Λ₀` restricts to a two-cocycle of `U`,
  which is a coboundary iff the projection `a ∈ Sym^n(ℂ²)` of its alternation
  `z(e₁, e₂) - z(e₂, e₁)` to the `U`-coinvariants vanishes. The projected alternation
  `(u, v) ↦ π(z(u, v) - z(v, u))` is an alternating biadditive form on `ℤ²`, hence equal to
  `det(u, v) • a`, and conjugating by the Levi elements `diag(A, 1)` shows
  `A · a = det(A) • a` for every `A ∈ GL₂(ℤ)`. So `a` is `SL₂(ℤ)`-invariant, hence zero.
* **The edge target vanishes.** The central element `-1 ∈ GL₂(ℤ)` acts on
  `Sym^{n+1} ⊗ det⁻¹` by `-1`, which kills `H¹(GL₂(ℤ), Sym^{n+1} ⊗ det⁻¹)`.
* By injectivity of the Hochschild–Serre edge on the kernel of restriction to `U`, every class
  vanishes. The ambient homogeneous `H²(Λ₀, V)`, which is the local cohomology at the
  identity-plane cusp, therefore vanishes too.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

open GeneralEisenstein GeneralEisenstein.Homogeneous GeneralEisenstein.Adelic Matrix
open TernaryPeriodPolynomials.SphericalDetection.Helpers

namespace TernaryPeriodPolynomials.Spectral.IdentityPlaneEven

/-! ### A central element acting by `-1` kills `H¹` -/

/-- If a central element acts by `-1`, then first cohomology vanishes. -/
theorem H1_eq_zero_of_central_neg {G : Type} [Group G] (W : Rep ℂ G) (c : G)
    (central : ∀ g, c * g = g * c) (negates : ∀ w, W.ρ c w = -w)
    (x : groupCohomology.H1 W) : x = 0 := by
  obtain ⟨z, rfl⟩ := oneCocycle_H1_surjective W x
  rw [groupCohomology.H1π_eq_zero_iff]
  refine ⟨-((2 : ℂ)⁻¹ • z c), ?_⟩
  funext g
  have left := (groupCohomology.mem_cocycles₁_iff z).mp z.property c g
  have right := (groupCohomology.mem_cocycles₁_iff z).mp z.property g c
  rw [central g, right, negates] at left
  rw [groupCohomology.d₀₁_hom_apply, map_neg, map_smul]
  have two : z g = (2 : ℂ)⁻¹ • z c - (2 : ℂ)⁻¹ • W.ρ g (z c) := by
    rw [← smul_sub]
    have doubled : (2 : ℂ) • z g = z c - W.ρ g (z c) := by
      rw [two_smul]
      linear_combination (norm := abel) left
    rw [← doubled, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  rw [two]
  abel

/-! ### Conjugation and the projected alternation -/

section Conjugation

variable {G A W : Type} [Group G] [CommGroup A] [AddCommGroup W] [Module ℂ W]

/-- Conjugating by `g` with `g⁻¹ u g = φ(u)` on the radical transforms the projected alternation
of a two-cocycle by the action `L` of `g` on the coinvariants. -/
theorem projected_alternation_conj (inclusion : A →* G) (representation : Rep ℂ G)
    (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector,
      projection (representation.ρ (inclusion radical) vector) = projection vector)
    (element : G) (φ : A →* A)
    (conjugates : ∀ radical, element⁻¹ * inclusion radical * element = inclusion (φ radical))
    (L : W →ₗ[ℂ] W)
    (intertwines : ∀ vector, projection (representation.ρ element vector) = L (projection vector))
    (cycle : groupCohomology.cocycles₂ representation) (first second : A) :
    L (projection (cycle (inclusion (φ first), inclusion (φ second)) -
        cycle (inclusion (φ second), inclusion (φ first)))) =
      projection (cycle (inclusion first, inclusion second) -
        cycle (inclusion second, inclusion first)) := by
  have equation0 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation
    element cycle (inclusion first) (inclusion second))
  have equation1 := congrArg projection (conjugationTwoCocycleHomotopy_boundary representation
    element cycle (inclusion second) (inclusion first))
  simp only [twoBoundaryCycle_apply, map_add, map_sub, radical_trivial, intertwines,
    conjugates] at equation0 equation1
  rw [← map_mul, mul_comm first second, map_mul] at equation0
  rw [map_sub, map_sub, map_sub]
  linear_combination (norm := abel) equation1 - equation0

/-- The projected alternation is additive in its first argument. -/
theorem projected_alternation_mul (inclusion : A →* G) (representation : Rep ℂ G)
    (projection : representation →ₗ[ℂ] W)
    (radical_trivial : ∀ radical vector,
      projection (representation.ρ (inclusion radical) vector) = projection vector)
    (cycle : groupCohomology.cocycles₂ representation) (first second third : A) :
    projection (cycle (inclusion (first * second), inclusion third) -
        cycle (inclusion third, inclusion (first * second))) =
      projection (cycle (inclusion first, inclusion third) -
          cycle (inclusion third, inclusion first)) +
        projection (cycle (inclusion second, inclusion third) -
          cycle (inclusion third, inclusion second)) := by
  let projected : A × A → W := fun pair => projection (cycle (inclusion pair.1, inclusion pair.2))
  have relation (left middle right : A) : projected (left * middle, right) +
      projected (left, middle) = projected (middle, right) + projected (left, middle * right) := by
    have equation := congrArg projection (twoCocycle_relation representation cycle
      (inclusion left) (inclusion middle) (inclusion right))
    simpa only [map_add, radical_trivial, projected, map_mul] using equation
  have h := abelianTwoCocycleAlternation_mul projected relation first second third
  simpa only [map_sub, projected] using h

end Conjugation

/-! ### Alternating biadditive forms on `ℤ²` -/

section Lattice

variable {W : Type} [AddCommGroup W]

theorem additive_decomposition (f : ℤ × ℤ →+ W) (x : ℤ × ℤ) :
    f x = x.1 • f (1, 0) + x.2 • f (0, 1) := by
  have hx : x = x.1 • ((1 : ℤ), (0 : ℤ)) + x.2 • ((0 : ℤ), (1 : ℤ)) := by
    ext <;> simp
  conv_lhs => rw [hx]
  rw [map_add, map_zsmul, map_zsmul]

/-- An alternating form on `ℤ²`, additive in the first argument, is `det • (its value at
`(e₁, e₂)`)`. -/
theorem alternating_eq_det (alt : RadicalLattice → RadicalLattice → W)
    (additive : ∀ x y z, alt (x * y) z = alt x z + alt y z)
    (anti : ∀ x y, alt x y = -alt y x) (diagonal : ∀ x, alt x x = 0) (u v : RadicalLattice) :
    alt u v = (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) •
      alt radicalLatticeFirst radicalLatticeSecond := by
  let f : RadicalLattice → ℤ × ℤ →+ W := fun w =>
    { toFun := fun x => alt (Multiplicative.ofAdd x) w
      map_zero' := by
        have h := additive 1 1 w
        rw [one_mul] at h
        change alt 1 w = 0
        simpa using h
      map_add' := fun x y => additive (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) w }
  have hf : ∀ w x, alt x w = x.toAdd.1 • alt radicalLatticeFirst w +
      x.toAdd.2 • alt radicalLatticeSecond w := fun w x => additive_decomposition (f w) x.toAdd
  rw [hf v u, anti radicalLatticeFirst v, anti radicalLatticeSecond v, hf radicalLatticeFirst v,
    hf radicalLatticeSecond v, diagonal, diagonal, anti radicalLatticeSecond radicalLatticeFirst]
  simp only [smul_zero, add_zero, zero_add, smul_neg, neg_neg, smul_smul, sub_smul]
  abel

end Lattice

/-! ### The restriction to the radical vanishes in even degree -/

variable (n : ℕ)

theorem map_sub_eq_neg_map_sub {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N]
    [Module ℂ N] (f : M →ₗ[ℂ] N) (a b : M) : f (a - b) = -f (b - a) := by
  rw [← map_neg, neg_sub]

/-- The projected alternation of an identity-plane two-cocycle on the radical. -/
def alternation (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n))
    (u v : RadicalLattice) : Binary.HomogeneousPoly n :=
  binaryHomogeneousRestrict n (cycle (identityPlaneRadicalInclusion u, identityPlaneRadicalInclusion v) -
    cycle (identityPlaneRadicalInclusion v, identityPlaneRadicalInclusion u))

theorem alternation_eq_det (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n))
    (u v : RadicalLattice) :
    alternation n cycle u v = (u.toAdd.1 * v.toAdd.2 - u.toAdd.2 * v.toAdd.1) •
      alternation n cycle radicalLatticeFirst radicalLatticeSecond := by
  apply alternating_eq_det (alternation n cycle)
  · exact projected_alternation_mul identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)
      (binaryHomogeneousRestrict n) (binaryHomogeneousRestrict_upperLattice n) cycle
  · intro x y
    exact map_sub_eq_neg_map_sub (binaryHomogeneousRestrict n) _ _
  · intro x
    rw [alternation, sub_self]
    exact LinearMap.map_zero _

theorem identityPlaneLevi_conjugates (matrix : GeneralLinearGroup (Fin 2) ℤ)
    (radical : RadicalLattice) :
    (identityPlaneLeviSection matrix)⁻¹ * identityPlaneRadicalInclusion radical *
        identityPlaneLeviSection matrix =
      identityPlaneRadicalInclusion (upperLeviLatticeInput matrix radical) := by
  apply Subtype.ext
  change (arithmeticLevi matrix)⁻¹ * upperRadicalLattice radical * arithmeticLevi matrix =
    upperRadicalLattice (upperLeviLatticeInput matrix radical)
  rw [mul_assoc, upperLeviLatticeInput_conjugation, inv_mul_cancel_left]

/-- The Levi element `diag(A, 1)` transforms the projected alternation by `A`. -/
theorem alternation_levi (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n))
    (matrix : GeneralLinearGroup (Fin 2) ℤ) (u v : RadicalLattice) :
    Binary.homogeneousAction n (-1) (GeneralLinearGroup.map (Int.castRingHom ℂ) matrix)
        (alternation n cycle (upperLeviLatticeInput matrix u) (upperLeviLatticeInput matrix v)) =
      alternation n cycle u v :=
  projected_alternation_conj identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)
    (binaryHomogeneousRestrict n) (binaryHomogeneousRestrict_upperLattice n)
    (identityPlaneLeviSection matrix) (upperLeviLatticeInput matrix)
    (identityPlaneLevi_conjugates matrix) _ (binaryHomogeneousRestrict_arithmeticLevi n matrix)
    cycle u v

/-- The projected alternation at `(e₁, e₂)` is `SL₂(ℤ)`-invariant. -/
theorem alternation_modular_fixed (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n))
    (g : SpecialLinearGroup (Fin 2) ℤ) :
    (ModularSymDimension.symRep n (-1)).ρ g
        (alternation n cycle radicalLatticeFirst radicalLatticeSecond) =
      alternation n cycle radicalLatticeFirst radicalLatticeSecond := by
  have h := alternation_levi n cycle (SpecialLinearGroup.toGL g) radicalLatticeFirst
    radicalLatticeSecond
  rw [alternation_eq_det n cycle (upperLeviLatticeInput _ radicalLatticeFirst)] at h
  have hinv : ((SpecialLinearGroup.toGL g)⁻¹ : GeneralLinearGroup (Fin 2) ℤ).val =
      ((g⁻¹ : SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← map_inv]
    rfl
  have hdet := (g⁻¹).property
  rw [Matrix.det_fin_two] at hdet
  have hone : ((upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeFirst).toAdd.1 *
        (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeSecond).toAdd.2 -
      (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeFirst).toAdd.2 *
        (upperLeviLatticeInput (SpecialLinearGroup.toGL g) radicalLatticeSecond).toAdd.1) = 1 := by
    simp only [upperLeviLatticeInput, radicalLatticeFirst, radicalLatticeSecond, MonoidHom.coe_mk,
      OneHom.coe_mk, toAdd_ofAdd, hinv, mul_one, mul_zero, add_zero, zero_add]
    linear_combination hdet
  rw [hone, one_smul] at h
  exact h

/-- **For even `n > 0`, the projected alternation vanishes.** -/
theorem alternation_eq_zero (hn : 0 < n)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n)) :
    alternation n cycle radicalLatticeFirst radicalLatticeSecond = 0 := by
  have hmem : alternation n cycle radicalLatticeFirst radicalLatticeSecond ∈
      ModularH1.fixedSpace (ModularSymDimension.symRep n (-1)) ModularGroup.S ⊓
        ModularH1.fixedSpace (ModularSymDimension.symRep n (-1)) modularOrderSix :=
    (ModularH1.mem_inf_fixed_iff (ModularSymDimension.symRep n (-1)) _).mpr
      (alternation_modular_fixed n cycle)
  rw [ModularSymDimension.inf_fixed_eq_bot hn (-1)] at hmem
  exact (Submodule.mem_bot ℂ).mp hmem

/-- Every identity-plane two-cocycle restricts to a coboundary on the radical (`n > 0`). -/
theorem twoCocycle_restriction_zero (hn : 0 < n)
    (cycle : groupCohomology.cocycles₂ (identityPlaneCoefficientRep n)) :
    groupCohomology.H2π (upperRadicalLatticeRep n)
      (twoCocycleRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep n) cycle) =
        0 :=
  (upperRadicalTwoCocycle_H2_zero_iff n hn _).mpr (alternation_eq_zero n hn cycle)

theorem H2_restriction_zero (hn : 0 < n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRep n)) :
    twoCohomologyRestriction identityPlaneRadicalInclusion (identityPlaneCoefficientRep n)
      cohomology = 0 := by
  obtain ⟨cycle, rfl⟩ := twoCocycle_H2_surjective (identityPlaneCoefficientRep n) cohomology
  rw [twoCohomologyRestriction_apply]
  exact twoCocycle_restriction_zero n hn cycle

/-! ### The edge target vanishes in even degree -/

theorem scalar_neg_one_central (g : GeneralLinearGroup (Fin 2) ℤ) :
    GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ) * g = g * GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ) := by
  apply Units.ext
  simp [GeneralLinearGroup.coe_scalar]

/-- `-1` acts by `-1` on `Sym^d ⊗ det^τ` for odd `d`. -/
theorem binary_homogeneousAction_neg_one {d : ℕ} (hd : Odd d) (τ : ℤ)
    (p : Binary.HomogeneousPoly d) :
    Binary.homogeneousAction d τ (GeneralLinearGroup.scalar (Fin 2) (-1 : ℂˣ)) p = -p := by
  apply Subtype.ext
  rw [Binary.homogeneousAction_coe, Binary.action_apply, ← map_inv, GeneralLinearGroup.coe_scalar,
    binary_substitute_scalar]
  simp [Binary.determinantCharacter, hd.neg_one_pow]

theorem scalar_neg_one_negates {d : ℕ} (hd : Odd d) (τ : ℤ) (w : arithmeticBinaryRep d τ) :
    (arithmeticBinaryRep d τ).ρ (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ)) w = -w := by
  have h : ∀ p : Binary.HomogeneousPoly d, Binary.homogeneousAction d τ
      (GeneralLinearGroup.map (Int.castRingHom ℂ) (GeneralLinearGroup.scalar (Fin 2) (-1 : ℤˣ))) p =
        -p := by
    intro p
    rw [GeneralLinearGroup.map_scalar]
    convert binary_homogeneousAction_neg_one hd τ p using 4
    apply Units.ext
    simp
  exact h w

/-- **`H¹(GL₂(ℤ), Sym^d ⊗ det^τ) = 0` for odd `d` and every twist `τ`**: the central element `-1`
acts by `-1`. -/
theorem arithmeticH1_eq_zero_of_odd (d : ℕ) (hd : Odd d) (τ : ℤ)
    (x : groupCohomology.H1 (arithmeticBinaryRep d τ)) : x = 0 :=
  H1_eq_zero_of_central_neg _ _ scalar_neg_one_central (scalar_neg_one_negates hd τ) x

theorem binaryH1_eq_zero (heven : Even n)
    (x : groupCohomology.H1 (arithmeticBinaryRep (n + 1) (-1))) : x = 0 :=
  arithmeticH1_eq_zero_of_odd (n + 1) heven.add_one (-1) x

/-! ### Vanishing of `H²(Λ₀, V)` -/

/-- **`H²(Λ₀, Sym^n ⊗ det⁻¹) = 0` for even `n > 0`** (group cohomology). -/
theorem groupH2_eq_zero (hn : 0 < n) (heven : Even n)
    (cohomology : groupCohomology.H2 (identityPlaneCoefficientRep n)) : cohomology = 0 := by
  have hker := H2_restriction_zero n hn cohomology
  have hedge : identityPlaneBinaryEdge n ⟨cohomology, hker⟩ = identityPlaneBinaryEdge n 0 :=
    (binaryH1_eq_zero n heven _).trans (binaryH1_eq_zero n heven _).symm
  exact congrArg Subtype.val (identityPlaneBinaryEdge_injective n hedge)

/-- **The ambient homogeneous `H²(Λ₀, V)` vanishes for even `n > 0`.** -/
theorem ambientH2_eq_zero (hn : 0 < n) (heven : Even n)
    (x : H2 (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
      (rationalCoefficientComponent n trivialCharacter)) : x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | _ C =>
  change classOf (flagArithmeticStabilizer .plane (QuotientGroup.mk (1 : RationalGL3)))
    (rationalCoefficientComponent n trivialCharacter) C = 0
  rw [classOf_eq_zero_iff]
  exact (ambientCocycle_H2_zero_iff _ _ C).mp (groupH2_eq_zero n hn heven _)

open CuspReduction

/-- **The local cohomology at the identity-plane cusp vanishes for even `n > 0`.** -/
theorem cuspH2_identityPlane_eq_zero (hn : 0 < n) (heven : Even n)
    (x : CuspH2 n trivialCharacter .plane false) : x = 0 :=
  ambientH2_eq_zero n hn heven x

theorem cuspH2_identityPlane_subsingleton (hn : 0 < n) (heven : Even n) :
    Subsingleton (CuspH2 n trivialCharacter .plane false) :=
  ⟨fun x y => (cuspH2_identityPlane_eq_zero n hn heven x).trans
    (cuspH2_identityPlane_eq_zero n hn heven y).symm⟩

/-- For even `n > 0` the local joint generalized eigenspace at the identity-plane cusp is zero. -/
theorem localJoint_identityPlane_eq_bot (hn : 0 < n) (heven : Even n)
    (c : HeckeCorrespondence → ℂ) : localJoint n trivialCharacter c .plane false = ⊥ := by
  rw [eq_bot_iff]
  intro x _
  rw [Submodule.mem_bot]
  exact cuspH2_identityPlane_eq_zero n hn heven x

end TernaryPeriodPolynomials.Spectral.IdentityPlaneEven
