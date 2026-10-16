module

public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.Parabolic.DualityIndexTwo
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.EpsilonCore
public import TernaryPeriodPolynomials.ArithmeticCohomology.BoundaryDuality.BinaryPairing
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.InnerParabolic
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.ExplicitBinaryAction
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.ParabolicBounds

@[expose] public section


/-!
# Parabolic Poincaré duality for `Γ₁'(3)`

`Γ₁'(3) = {A ∈ GL₂(ℤ) : second row ≡ (0, 1) mod 3}` is the union of the congruence subgroup
`Γ₁(3) = ⟨T, L⟩ = ℤ * ℤ/3` and `Γ₁(3) ε`, where `ε = diag(-1, 1)` inverts `T` and `L`.  For a
complex representation `ρ` of `Γ₁'(3)`, the *parabolic* classes of `H¹(Γ₁'(3), ρ)` (crossed
homomorphisms modulo coboundaries) are the classes of the crossed homomorphisms `z` whose values at
`T` and at `L` are coboundaries (`z T = T u - u`, `z L = L u' - u'`); such a crossed homomorphism has
a primitive triple at the three special elements `T`, `L⁻¹`, `(T L⁻¹)⁻¹` of `Γ₁(3)` (the last has
order three).

For a perfect pairing `B : V × W → ℂ` of two representations which is `Γ₁(3)`-invariant and odd under
`ε` (the determinant twist), the cup pairing on the parabolic classes, computed on the fundamental
two-chain of the sphere with two cusps and one cone point, is a bilinear form which is left
nondegenerate: a parabolic class pairing to zero with every parabolic class is zero.  The classes
which vanish at every cusp frame of `Γ₁'(3)` (the subspace `binaryParabolicH1` of the bad-line
Levi cohomology) are parabolic in this sense.

Original work by Claude Sonnet 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality

open TripleModel LinearDuality CocycleBridge EpsilonSplit
open TernaryPeriodPolynomials.LevelThree
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators GammaOneThree
open Matrix

namespace LevelThree

/-- Elements of `Γ₁(3)` have determinant one. -/
theorem det_core (k : core) : GeneralLinearGroup.det (k : binaryArithmeticLevel).val = 1 := by
  obtain ⟨k, hk⟩ := k
  change GeneralLinearGroup.det k.val = 1
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, upper, Matrix.det_fin_two_of]
    · apply Units.ext
      simp [GeneralLinearGroup.val_det_apply, lower, Matrix.det_fin_two_of]
  | one => simp
  | mul x y _ _ hx hy => rw [Subgroup.coe_mul, map_mul, hx, hy, one_mul]
  | inv x _ hx => rw [Subgroup.coe_inv, map_inv, hx, inv_one]

/-- `ε` is not in `Γ₁(3)`. -/
theorem reflection_not_mem_core : reflection ∉ core := by
  intro h
  have h1 : GeneralLinearGroup.det (reflection : binaryArithmeticLevel).val = 1 :=
    det_core ⟨reflection, h⟩
  have h2 : GeneralLinearGroup.det (reflection : binaryArithmeticLevel).val = -1 := by
    apply Units.ext
    simp [GeneralLinearGroup.val_det_apply, reflection, Matrix.det_fin_two_of]
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- `Γ₁'(3)` is the union of `Γ₁(3)` and `Γ₁(3) ε`, with `ε` acting by the involution `coreSigma`. -/
theorem indexTwo : IndexTwo (core.subtype : core →* binaryArithmeticLevel) reflection
    EpsilonCore.coreSigma where
  inj := Subtype.val_injective
  sq := reflection_mul_self
  conj := fun n => EpsilonCore.coreSigma_coe n
  cover := by
    intro g
    rcases mem_core_or g with hg | hg
    · exact Or.inl ⟨⟨g, hg⟩, rfl⟩
    · refine Or.inr ⟨⟨g * reflection, hg⟩, ?_⟩
      show g * reflection * reflection = g
      rw [mul_assoc, reflection_mul_self, mul_one]
  not_mem := by
    intro n h
    have h' : (n : binaryArithmeticLevel) = reflection := h
    exact reflection_not_mem_core (h' ▸ n.property)

section Primitives

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/-- A crossed homomorphism of `Γ₁(3)` whose values at `T` and `L` are coboundaries has a primitive
triple at `T`, `L⁻¹`, `(T L⁻¹)⁻¹`. -/
theorem exists_primitive_of_cusps {ρ : Representation ℂ core V} {z : core → V}
    (hz : IsCocycle ρ z) (hT : ∃ u : V, z coreT = (ρ coreT - 1) u)
    (hL : ∃ u : V, z coreL = (ρ coreL - 1) u) :
    ∃ v : V × V × V, IsPrimitive ρ coreT coreL⁻¹ z v :=
  exists_primitive_of_exists hT (exists_sub_inv hz hL)
    (exists_sub_of_pow hz (by norm_num : 0 < 3) (by rw [inv_pow, core_elliptic_cube, inv_one]))

/-- Conversely a primitive triple gives coboundaries at `T` and `L`. -/
theorem exists_cusps_of_primitive {ρ : Representation ℂ core V} {z : core → V}
    (hz : IsCocycle ρ z) {v : V × V × V} (hv : IsPrimitive ρ coreT coreL⁻¹ z v) :
    (∃ u : V, z coreT = (ρ coreT - 1) u) ∧ ∃ u : V, z coreL = (ρ coreL - 1) u := by
  refine ⟨⟨v.1, hv.1⟩, ?_⟩
  obtain ⟨u, hu⟩ := exists_sub_inv hz (g := coreL⁻¹) ⟨v.2.1, hv.2.1⟩
  rw [inv_inv] at hu
  exact ⟨u, hu⟩

end Primitives

section Model

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A crossed homomorphism is zero in the crossed `H¹` iff it is a coboundary. -/
theorem crossed_mkQ_eq_zero_iff {G : Type} [Group G] (ρ : Representation ℂ G V)
    (x : crossedCocycles ρ) :
    (crossedBoundaries ρ).mkQ x = 0 ↔ ∃ u : V, ∀ γ, x.1 γ = ρ γ u - u := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, fun γ => (congrArg (fun y : crossedCocycles ρ => y.1 γ) hu).symm⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, Subtype.ext (funext fun γ => (hu γ).symm)⟩

/-- Every crossed homomorphism is an element of the crossed-homomorphism module. -/
theorem exists_crossedCocycle_of_isCocycle {G : Type} [Group G] (ρ : Representation ℂ G V)
    (Z : G → V) (hZ : IsCocycle ρ Z) : ∃ y : crossedCocycles ρ, (crossedCocycles ρ).subtype y = Z :=
  ⟨⟨Z, hZ⟩, rfl⟩

/-- Elements of the crossed-homomorphism module are crossed homomorphisms. -/
theorem isCocycle_crossed {G : Type} [Group G] (ρ : Representation ℂ G V) (x : crossedCocycles ρ) :
    IsCocycle ρ x.1 := x.2

variable (ρ : Representation ℂ binaryArithmeticLevel V)
  (ρ' : Representation ℂ binaryArithmeticLevel W)

/-- **The parabolic crossed homomorphisms of `Γ₁'(3)`**: those whose restriction to `Γ₁(3)` has a
primitive triple at `T`, `L⁻¹`, `(T L⁻¹)⁻¹`. -/
abbrev parabolicCrossed : Submodule ℂ (crossedCocycles ρ) :=
  parabolicSub core.subtype ρ coreT coreL⁻¹ (crossedCocycles ρ).subtype

/-- **The parabolic classes of `H¹(Γ₁'(3), ρ)`** in the crossed-homomorphism model. -/
abbrev parabolicCrossedH1 : Submodule ℂ (CrossedH1 ρ) :=
  parabolicClasses core.subtype ρ coreT coreL⁻¹ (crossedCocycles ρ).subtype
    (crossedBoundaries ρ).mkQ

/-- A crossed homomorphism is parabolic iff its values at `T` and `L` are coboundaries. -/
theorem mem_parabolicCrossed_iff (x : crossedCocycles ρ) :
    x ∈ parabolicCrossed ρ ↔
      (∃ u : V, x.1 (upper 1) = ρ (upper 1) u - u) ∧ ∃ u : V, x.1 (lower 1) = ρ (lower 1) u - u := by
  constructor
  · intro hx
    obtain ⟨hc, v, hv⟩ := mem_parabolicCochains.mp (mem_parabolicSub.mp hx)
    exact exists_cusps_of_primitive (isCocycle_comp hc core.subtype) hv
  · rintro ⟨hT, hL⟩
    refine mem_parabolicSub.mpr (mem_parabolicCochains.mpr ⟨isCocycle_crossed ρ x, ?_⟩)
    exact exists_primitive_of_cusps (isCocycle_comp (isCocycle_crossed ρ x) core.subtype) hT hL

/-- The hypotheses on a pairing `B : V × W → ℂ` of representations of `Γ₁'(3)`: perfect, invariant
under `Γ₁(3)` and odd under `ε = diag(-1, 1)` (twisted by the determinant). -/
structure TwistedPairing (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) : Prop where
  left : ∀ v : V, (∀ w : W, B v w = 0) → v = 0
  right : ∀ w : W, (∀ v : V, B v w = 0) → w = 0
  special : ∀ (g : core) (v : V) (w : W), B (ρ g.1 v) (ρ' g.1 w) = B v w
  odd : ∀ (v : V) (w : W), B (ρ reflection v) (ρ' reflection w) = (-1 : ℂ) * B v w

variable {ρ ρ'} {B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ}

/-- **Left nondegeneracy of the `ε`-invariant parabolic crossed homomorphisms of `Γ₁(3)`**, in the
form required by the descent to `Γ₁'(3)`. -/
theorem nlevelND [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (P : TwistedPairing ρ ρ' B) :
    NLevelND core.subtype ρ ρ' B coreT coreL⁻¹ reflection EpsilonCore.coreSigma := by
  intro z hz v hv hinvz zero
  exact EpsilonCore.left_nondegenerate ρ ρ' P.left P.right P.special P.odd hz hv hinvz zero

/-- **The parabolic cup pairing on `H¹(Γ₁'(3), ·)`**: the bilinear form on the parabolic classes
given on representatives by the cup formula of the restrictions to `Γ₁(3)`, computed from a primitive
triple of the first class (`parabolicPairing_apply`). -/
def parabolicPairing (P : TwistedPairing ρ ρ' B) :
    parabolicCrossedH1 ρ →ₗ[ℂ] parabolicCrossedH1 ρ' →ₗ[ℂ] ℂ :=
  classPairing core.subtype ρ ρ' B coreT coreL⁻¹ (fun n v w => P.special n v w)
    (crossedCocycles ρ).subtype (crossedCocycles ρ').subtype (crossedBoundaries ρ).mkQ
    (crossedBoundaries ρ').mkQ (fun x h => (crossed_mkQ_eq_zero_iff ρ x).1 h)
    (fun y h => (crossed_mkQ_eq_zero_iff ρ' y).1 h)

/-- **The value of the parabolic cup pairing on representatives.** -/
theorem parabolicPairing_apply (P : TwistedPairing ρ ρ' B) (x : crossedCocycles ρ)
    (y : crossedCocycles ρ') (hx : x ∈ parabolicCrossed ρ) (hy : y ∈ parabolicCrossed ρ')
    {v : V × V × V}
    (hv : IsPrimitive (ρ.comp core.subtype) coreT coreL⁻¹ (fun n => x.1 (core.subtype n)) v) :
    parabolicPairing P ⟨(crossedBoundaries ρ).mkQ x, Submodule.mem_map_of_mem hx⟩
        ⟨(crossedBoundaries ρ').mkQ y, Submodule.mem_map_of_mem hy⟩ =
      cupFormula B (ρ'.comp core.subtype) coreT coreL⁻¹ (fun n => x.1 (core.subtype n))
        (fun n => y.1 (core.subtype n)) v :=
  classPairing_eq_cupFormula core.subtype ρ ρ' B coreT coreL⁻¹ (fun n v w => P.special n v w)
    (crossedCocycles ρ).subtype (crossedCocycles ρ').subtype (crossedBoundaries ρ).mkQ
    (crossedBoundaries ρ').mkQ (fun x h => (crossed_mkQ_eq_zero_iff ρ x).1 h)
    (fun y h => (crossed_mkQ_eq_zero_iff ρ' y).1 h) ⟨x, hx⟩ ⟨y, hy⟩
    (Submodule.mem_map_of_mem hx) (Submodule.mem_map_of_mem hy) hv

/-- **Left nondegeneracy of the parabolic cup pairing of `Γ₁'(3)`** (parabolic Poincaré duality): a
parabolic class of `H¹(Γ₁'(3), ρ)` which pairs to zero with every parabolic class of
`H¹(Γ₁'(3), ρ')` is zero. -/
theorem parabolicPairing_left_nondegenerate [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (P : TwistedPairing ρ ρ' B) (cl : parabolicCrossedH1 ρ)
    (h : ∀ cl' : parabolicCrossedH1 ρ', parabolicPairing P cl cl' = 0) : cl = 0 :=
  classPairing_left_nondegenerate core.subtype ρ ρ' B coreT coreL⁻¹ (fun n v w => P.special n v w)
    (crossedCocycles ρ).subtype (crossedCocycles ρ').subtype (crossedBoundaries ρ).mkQ
    (crossedBoundaries ρ').mkQ (fun x => crossed_mkQ_eq_zero_iff ρ x)
    (fun y h => (crossed_mkQ_eq_zero_iff ρ' y).1 h) (exists_crossedCocycle_of_isCocycle ρ')
    (cochainNondegenerate_of_nd indexTwo ρ ρ' B coreT coreL⁻¹ (fun n v w => P.special n v w)
      (nlevelND P))
    cl h

end Model

section Sol

/-- The permutation matrix swapping the two coordinates, as a frame over `ℚ`. -/
def swapQ : GeneralLinearGroup (Fin 2) ℚ :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/-- The swap matrix is an involution. -/
theorem swapQ_mul_self : swapQ * swapQ = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapQ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The swap matrix is its own inverse. -/
theorem swapQ_inv : swapQ⁻¹ = swapQ := inv_eq_of_mul_eq_one_right swapQ_mul_self

/-- `T` lies in the stabilizer of the cusp `∞`. -/
theorem upper_mem_binaryCuspLevel_one : upper 1 ∈ binaryCuspLevel 1 := by
  rw [mem_binaryCuspLevel_iff]
  rw [inv_one, one_mul, mul_one]
  change ((upper 1).val.val.map (Int.castRingHom ℚ)) 1 0 = 0
  simp [upper]

/-- `L` lies in the stabilizer of the cusp `0`. -/
theorem lower_mem_binaryCuspLevel_swap : lower 1 ∈ binaryCuspLevel swapQ := by
  rw [mem_binaryCuspLevel_iff, swapQ_inv]
  change (swapQ.val * ((lower 1).val.val.map (Int.castRingHom ℚ)) * swapQ.val) 1 0 = 0
  simp [swapQ, lower, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

/-- **The classes vanishing at every cusp frame are parabolic**: `binaryParabolicH1` (the classes
whose restriction to every cusp stabilizer `binaryCuspLevel frame` is a coboundary) lies in the
parabolic classes (the cusps `1` and `swapQ` give the conditions at `T` and `L`). -/
theorem binaryParabolicH1_le (degree : ℕ) :
    binaryParabolicH1 degree ≤ parabolicCrossedH1 (binaryArithmeticRepresentation degree) := by
  intro x hx
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have key : ∀ frame : GeneralLinearGroup (Fin 2) ℚ,
      ∃ u, ∀ γ : binaryCuspLevel frame, y.1 γ.1 = binaryArithmeticRepresentation degree γ.1 u - u := by
    intro frame
    have h0 := LinearMap.mem_ker.mp
      ((Submodule.mem_iInf (M := CrossedH1 (binaryArithmeticRepresentation degree)) _).mp hx frame)
    have h1 : (crossedBoundaries ((binaryArithmeticRepresentation degree).comp
        (binaryCuspLevel frame).subtype)).mkQ
        (crossedPullbackCocycles (binaryCuspLevel frame).subtype
          (binaryArithmeticRepresentation degree) y) = 0 := h0
    exact (crossed_mkQ_eq_zero_iff _ _).1 h1
  have hmem : y ∈ parabolicCrossed (binaryArithmeticRepresentation degree) := by
    rw [mem_parabolicCrossed_iff]
    constructor
    · obtain ⟨u, hu⟩ := key 1
      exact ⟨u, hu ⟨upper 1, upper_mem_binaryCuspLevel_one⟩⟩
    · obtain ⟨u, hu⟩ := key swapQ
      exact ⟨u, hu ⟨lower 1, lower_mem_binaryCuspLevel_swap⟩⟩
  exact Submodule.mem_map_of_mem hmem

end Sol

section BinaryForms

/-- Elements of `Γ₁(3)` have determinant one in `GL₂(ℂ)`. -/
theorem complex_det_core (g : core) :
    ((Matrix.GeneralLinearGroup.det
      (binaryIntegralComplex (g : binaryArithmeticLevel).val) : ℂˣ) : ℂ) = 1 := by
  have h := det_core g
  rw [GeneralLinearGroup.val_det_apply]
  have hdet := RingHom.map_det (Int.castRingHom ℂ) (g : binaryArithmeticLevel).val.val
  change (RingHom.mapMatrix (Int.castRingHom ℂ) (g : binaryArithmeticLevel).val.val).det = 1
  rw [← hdet]
  have h' := congrArg (fun u : ℤˣ => (u : ℤ)) h
  simp only [GeneralLinearGroup.val_det_apply, Units.val_one] at h'
  rw [h', map_one]

/-- The determinant of `ε` in `GL₂(ℂ)` is `-1`. -/
theorem complex_det_reflection :
    ((Matrix.GeneralLinearGroup.det
      (binaryIntegralComplex (reflection : binaryArithmeticLevel).val) : ℂˣ) : ℂ) = -1 := by
  change ((reflection : binaryArithmeticLevel).val.val.map (Int.castRingHom ℂ)).det = -1
  simp [reflection, Matrix.det_fin_two]

/-- **The classical pairing of binary forms satisfies the hypotheses** for `Sym^m ⊗ det^e` and
`Sym^m ⊗ det^{e'}` when the total determinant twist `e + e' - m` is odd. -/
theorem twistedPairing_levelRep (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ))) :
    TwistedPairing (ParabolicBounds.levelRep m e) (ParabolicBounds.levelRep m e')
      (BinaryPairing.binaryPairing m) where
  left := fun v h => BinaryPairing.binaryPairing_left_eq_zero m h
  right := fun w h => BinaryPairing.binaryPairing_right_eq_zero m h
  special := by
    intro g v w
    exact BinaryPairing.binaryPairing_homogeneousAction_of_det_eq_one m e e'
      (binaryIntegralComplex (g : binaryArithmeticLevel).val) (Units.ext (complex_det_core g)) v w
  odd := by
    intro v w
    have h := BinaryPairing.binaryPairing_homogeneousAction m e e'
      (binaryIntegralComplex (reflection : binaryArithmeticLevel).val) v w
    rw [complex_det_reflection, hodd.neg_one_zpow] at h
    exact h

/-- **Parabolic Poincaré duality for binary forms on `Γ₁'(3)`**. -/
theorem levelRep_left_nondegenerate (m : ℕ) (e e' : ℤ) (hodd : Odd (e + e' - (m : ℤ)))
    (cl : parabolicCrossedH1 (ParabolicBounds.levelRep m e))
    (h : ∀ cl' : parabolicCrossedH1 (ParabolicBounds.levelRep m e'),
      parabolicPairing (twistedPairing_levelRep m e e' hodd) cl cl' = 0) : cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_levelRep m e e' hodd) cl h

/-- The bad-line coefficient system `Sym^{degree+1}` (untwisted) pairs with itself through
`binaryPairing (degree + 1)` when `degree` is even. -/
theorem twistedPairing_binaryArithmeticRepresentation (degree : ℕ) (heven : Even degree) :
    TwistedPairing (binaryArithmeticRepresentation degree) (binaryArithmeticRepresentation degree)
      (BinaryPairing.binaryPairing (degree + 1)) :=
  twistedPairing_levelRep (degree + 1) 0 0 (by
    obtain ⟨k, hk⟩ := heven
    exact ⟨-(k : ℤ) - 1, by omega⟩)

/-- **Parabolic Poincaré duality for the bad-line Levi** `CrossedH1 (binaryArithmeticRepresentation
degree)`, for even `degree`: a parabolic class pairing to zero with every parabolic class is zero. -/
theorem binaryArithmeticRepresentation_left_nondegenerate (degree : ℕ) (heven : Even degree)
    (cl : parabolicCrossedH1 (binaryArithmeticRepresentation degree))
    (h : ∀ cl' : parabolicCrossedH1 (binaryArithmeticRepresentation degree),
      parabolicPairing (twistedPairing_binaryArithmeticRepresentation degree heven) cl cl' = 0) :
    cl = 0 :=
  parabolicPairing_left_nondegenerate (twistedPairing_binaryArithmeticRepresentation degree heven)
    cl h

end BinaryForms

end LevelThree

end TernaryPeriodPolynomials.BoundaryDuality.ParabolicDuality
