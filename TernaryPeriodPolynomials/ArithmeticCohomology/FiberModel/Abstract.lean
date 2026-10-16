module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Fiber.Comparison
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Full.ActionFrames
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Order.Interval.Set.Group
public import Mathlib.Algebra.Order.Ring.Interval
public import Mathlib.Data.Nat.NthRoot.Defs
public import Mathlib.GroupTheory.QuotientGroup.ModEq
public import Mathlib.Topology.Order.AtTopBotIxx

@[expose] public section


/-!
# The fiber model of `Hom_K(St, E)`, for an arbitrary coefficient module

Lemma 3.2 (`prop:26-model`) of the paper
identifies the equivariant homomorphisms from the Steinberg module (the ordinary incidence cycles
`TernaryPoly.OrdinaryIncidenceChains.Cycles`) to the coefficient module with the functions
`F : 𝒮 → E` on the 26 nonzero residue covectors satisfying the signed-permutation relations and the
norm relation.  This file proves it for an arbitrary `ℚ`-module `E` with a representation of
`GL₃(ℤ)`: the maps `Φ ↦ F_Φ`, `F ↦ Φ_F` are mutually inverse linear equivalences, and the
reference coordinate `F(ℓ)` is the value of `Φ` on the identity apartment.

The fiber system is written for the left action `ρ`: `F(r h) = sgn(π) ρ(h⁻¹) F(r)` for every
signed permutation matrix `h = D π`, and `F(r) + ρ(A) F(rA) + ρ(A²) F(rA²) = 0`.

Formalized by Claude Sonnet 5.5.  The construction of
`Φ_F` follows `TernaryPoly.OrdinaryFiberComparison.cycleMap` (which treats only the polynomial
module with determinant exponent `-1`); the converse direction is new.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.FiberModel

open TernaryPoly TernaryPoly.ModThreeGoodAction TernaryPoly.OrdinaryCovectors
  TernaryPoly.OrdinaryApartmentFrames TernaryPoly.OrdinaryApartmentPresentation

/-- The permutation matrix of a permutation, as an element of `GL₃(ℤ)`; its action on covectors is
`r ↦ r ∘ π`. -/
def permFrame : Equiv.Perm (Fin 3) →* IntegralGL :=
  (Matrix.permMatrixHom (R := ℤ) (n := Fin 3)).toHomUnits

@[simp] theorem permFrame_val (π : Equiv.Perm (Fin 3)) :
    (permFrame π).val = Equiv.Perm.permMatrix ℤ π⁻¹ := rfl

/-- The signed permutation matrix `D π`, where `D` has entry `-1` exactly on the set `s`. -/
def signedPerm (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) : IntegralGL :=
  signFrame s * permFrame π

/-- The action of `GL₃(ℤ)` on the nonzero residue covectors by right multiplication mod three. -/
def act (r : NonzeroCovector) (g : IntegralGL) : NonzeroCovector :=
  ⟨Matrix.vecMul r.1 (reduction g).val, by
    intro h
    apply r.2
    have hr : r.1 = Matrix.vecMul (Matrix.vecMul r.1 (reduction g).val) ((reduction g)⁻¹).val := by
      rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [hr, h, Matrix.zero_vecMul]⟩

theorem act_mul (r : NonzeroCovector) (g h : IntegralGL) : act r (g * h) = act (act r g) h := by
  apply Subtype.ext
  simp only [act, map_mul, Units.val_mul, Matrix.vecMul_vecMul]

@[simp] theorem act_one (r : NonzeroCovector) : act r 1 = r := by
  apply Subtype.ext
  simp [act]

/-- The residue covector of an integral frame, as a nonzero covector. -/
def rowS (g : IntegralGL) : NonzeroCovector := ⟨row g, row_ne_zero g⟩

theorem rowS_mul (g h : IntegralGL) : rowS (g * h) = act (rowS g) h :=
  Subtype.ext (row_mul g h)

theorem rowS_one : (rowS 1).1 = fixedRow := row_one

theorem act_surjective (r : NonzeroCovector) : ∃ g : IntegralGL, rowS g = r := by
  obtain ⟨g, hg⟩ := row_surjective r
  exact ⟨g, Subtype.ext hg⟩

theorem rowS_eq_iff (g h : IntegralGL) : rowS g = rowS h ↔ ∃ k : K, k.val * g = h := by
  rw [← row_eq_iff]
  exact Subtype.ext_iff

/-! ### The generators of the signed permutation group -/

theorem signFrame_empty : signFrame ∅ = 1 := by
  apply Units.ext
  change Matrix.diagonal (signEntry ∅) = 1
  have : signEntry ∅ = fun _ => 1 := by
    funext j
    simp [signEntry]
  rw [this]
  exact Matrix.diagonal_one

/-- The cyclic permutation whose matrix is the library generator `c`. -/
abbrev cyclePerm' : Equiv.Perm (Fin 3) := TernaryPoly.OrdinaryFiberPermutations.cyclePerm

/-- The transposition whose matrix is the library generator `s`. -/
abbrev swapPerm' : Equiv.Perm (Fin 3) := TernaryPoly.OrdinaryFiberPermutations.swapPerm

theorem permFrame_cycle : permFrame cyclePerm' = ReferenceCoefficientMatrices.c ^ 2 := by
  rw [← ReferenceCoefficientMatrices.c_inv_eq_sq]
  apply Units.ext
  rw [permFrame_val]
  decide +kernel

theorem permFrame_swap : permFrame swapPerm' = ReferenceCoefficientMatrices.s := by
  apply Units.ext
  rw [permFrame_val]
  decide +kernel


/-! ### Frame cycles under signed permutations -/

theorem frameCycle_pow_c (x : IntegralGL) (a : ℕ) :
    frameCycle (x * ReferenceCoefficientMatrices.c ^ a) = frameCycle x := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, ← mul_assoc, OrdinaryFullAction.frameCycle_cyclic, ih]

theorem frameCycle_pow_s (x : IntegralGL) (b : ℕ) :
    frameCycle (x * ReferenceCoefficientMatrices.s ^ b) = ((-1 : ℤ) ^ b) • frameCycle x := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [pow_succ, ← mul_assoc, OrdinaryFullAction.frameCycle_swap, ih, pow_succ]
    simp

theorem sign_cycle : (Equiv.Perm.sign cyclePerm' : ℤˣ) = 1 := by
  unfold cyclePerm' TernaryPoly.OrdinaryFiberPermutations.cyclePerm
  decide +kernel

theorem sign_swap : (Equiv.Perm.sign swapPerm' : ℤˣ) = -1 := by
  unfold swapPerm' TernaryPoly.OrdinaryFiberPermutations.swapPerm
  decide +kernel

/-- An apartment changes by the sign of the permutation under a signed permutation matrix. -/
theorem frameCycle_signedPerm (g : IntegralGL) (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) :
    frameCycle (g * signedPerm s π) = ((Equiv.Perm.sign π : ℤˣ) : ℤ) • frameCycle g := by
  obtain ⟨a, b, rfl⟩ := TernaryPoly.OrdinaryFiberPermutations.permutation_decomposition π
  have hsign : (Equiv.Perm.sign (cyclePerm' ^ a.val * swapPerm' ^ b.val) : ℤˣ) =
      (-1) ^ b.val := by
    rw [map_mul, map_pow, map_pow, sign_cycle, sign_swap, one_pow, one_mul]
  have hx : g * signedPerm s (cyclePerm' ^ a.val * swapPerm' ^ b.val) =
      ((g * signFrame s) * ReferenceCoefficientMatrices.c ^ (2 * a.val)) *
        ReferenceCoefficientMatrices.s ^ b.val := by
    rw [signedPerm, map_mul, map_pow, map_pow, permFrame_cycle, permFrame_swap, pow_mul]
    simp only [mul_assoc]
  rw [hx, frameCycle_pow_s, frameCycle_pow_c, OrdinaryFullAction.frameCycle_signFrame, hsign]
  simp

section Fibers

variable {E : Type*} [AddCommGroup E] [Module ℚ E] (ρ : Representation ℚ IntegralGL E)

theorem rho_mul_apply (g h : IntegralGL) (x : E) : ρ (g * h) x = ρ g (ρ h x) := by
  rw [map_mul, Module.End.mul_apply]

theorem rho_inv_cancel (h : IntegralGL) (x : E) : ρ h (ρ h⁻¹ x) = x := by
  rw [← rho_mul_apply, mul_inv_cancel, map_one, Module.End.one_apply]

theorem rho_inv_cancel' (h : IntegralGL) (x : E) : ρ h⁻¹ (ρ h x) = x := by
  rw [← rho_mul_apply, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The left side of the fiber norm relation. -/
def normExpr (F : NonzeroCovector → E) (r : NonzeroCovector) : E :=
  F r + ρ ReferenceCoefficientMatrices.a (F (act r ReferenceCoefficientMatrices.a)) +
    ρ (ReferenceCoefficientMatrices.a ^ 2) (F (act r (ReferenceCoefficientMatrices.a ^ 2)))

/-- The fiber system `F(r h) = sgn(π) ρ(h⁻¹) F(r)` (signed permutations `h = D π`) and
`F(r) + ρ(A) F(rA) + ρ(A²) F(rA²) = 0`. -/
structure IsFiberSystem (F : NonzeroCovector → E) : Prop where
  signed : ∀ (s : Finset (Fin 3)) (π : Equiv.Perm (Fin 3)) (r : NonzeroCovector),
    F (act r (signedPerm s π)) =
      ((Equiv.Perm.sign π : ℤˣ) : ℤ) • ρ (signedPerm s π)⁻¹ (F r)
  norm : ∀ r : NonzeroCovector, normExpr ρ F r = 0

/-- The fiber functions, as a `ℚ`-subspace of all functions on the nonzero covectors. -/
def fiberSpace : Submodule ℚ (NonzeroCovector → E) where
  carrier := {F | IsFiberSystem ρ F}
  zero_mem' := ⟨fun s π r => by simp, fun r => by simp [normExpr]⟩
  add_mem' := by
    intro F G hF hG
    refine ⟨fun s π r => ?_, fun r => ?_⟩
    · simp only [Pi.add_apply, map_add, smul_add]
      rw [hF.signed, hG.signed]
    · have h1 := hF.norm r
      have h2 := hG.norm r
      calc normExpr ρ (F + G) r = normExpr ρ F r + normExpr ρ G r := by
            simp only [normExpr, Pi.add_apply, map_add]
            abel
        _ = 0 := by rw [h1, h2, add_zero]
  smul_mem' := by
    intro c F hF
    refine ⟨fun s π r => ?_, fun r => ?_⟩
    · simp only [Pi.smul_apply, map_smul]
      rw [hF.signed]
      simp [smul_comm c]
    · have h1 := hF.norm r
      calc normExpr ρ (c • F) r = c • normExpr ρ F r := by
            simp only [normExpr, Pi.smul_apply, map_smul, smul_add]
        _ = 0 := by rw [h1, smul_zero]

theorem mem_fiberSpace {F : NonzeroCovector → E} : F ∈ fiberSpace ρ ↔ IsFiberSystem ρ F := Iff.rfl

variable {ρ}

theorem IsFiberSystem.sign {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) (s : Finset (Fin 3))
    (r : NonzeroCovector) : F (act r (signFrame s)) = ρ (signFrame s)⁻¹ (F r) := by
  have h := hF.signed s 1 r
  simpa [signedPerm] using h

theorem IsFiberSystem.cyclic {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F)
    (r : NonzeroCovector) :
    F (act r ReferenceCoefficientMatrices.c) = ρ ReferenceCoefficientMatrices.c⁻¹ (F r) := by
  have h := hF.signed ∅ cyclePerm' (act r ReferenceCoefficientMatrices.c)
  have e : ReferenceCoefficientMatrices.c * ReferenceCoefficientMatrices.c ^ 2 = 1 := by
    rw [← pow_succ']
    exact ReferenceCoefficientMatrices.c_cube
  rw [signedPerm, signFrame_empty, one_mul, permFrame_cycle, sign_cycle, ← act_mul, e, act_one] at h
  have h2 := congrArg (ρ (ReferenceCoefficientMatrices.c ^ 2)) h
  rw [Units.val_one, one_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at h2
  rw [ReferenceCoefficientMatrices.c_inv_eq_sq]
  exact h2.symm

theorem IsFiberSystem.swap {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F)
    (r : NonzeroCovector) :
    F (act r ReferenceCoefficientMatrices.s) = -ρ ReferenceCoefficientMatrices.s⁻¹ (F r) := by
  have h := hF.signed ∅ swapPerm' r
  rw [signedPerm, signFrame_empty, one_mul, permFrame_swap, sign_swap] at h
  rw [h]
  simp

/-- The frame values of a fiber system, satisfying all the integral apartment relations. -/
def frameValues {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) :
    TernaryPoly.OrdinaryApartmentEvaluation.FrameValues E where
  value g := ρ g (F (rowS g))
  lines g h he := by
    have hh : AugmentedFrameComplex.augmentedLine g 0 = AugmentedFrameComplex.augmentedLine h 0 ∧
        AugmentedFrameComplex.augmentedLine g 1 = AugmentedFrameComplex.augmentedLine h 1 ∧
        AugmentedFrameComplex.augmentedLine g 2 = AugmentedFrameComplex.augmentedLine h 2 := by
      simpa only [GoodRelativeChains.triangleList, List.cons.injEq, and_true] using he
    obtain ⟨s, rfl⟩ := eq_mul_signFrame_of_column_lines g h (by
      intro j
      fin_cases j
      · exact hh.1
      · exact hh.2.1
      · exact hh.2.2)
    rw [rowS_mul, hF.sign, rho_mul_apply, rho_inv_cancel]
  cyclic g := by
    rw [rowS_mul, hF.cyclic, rho_mul_apply, rho_inv_cancel]
  swap g := by
    rw [rowS_mul, hF.swap, map_neg, rho_mul_apply, rho_inv_cancel]
  norm g := by
    have h := hF.norm (rowS g)
    unfold normExpr at h
    have e : ρ g (F (rowS g)) + ρ (g * ReferenceCoefficientMatrices.a)
        (F (rowS (g * ReferenceCoefficientMatrices.a))) +
        ρ (g * ReferenceCoefficientMatrices.a ^ 2)
          (F (rowS (g * ReferenceCoefficientMatrices.a ^ 2))) =
        ρ g (F (rowS g) + ρ ReferenceCoefficientMatrices.a (F (act (rowS g) ReferenceCoefficientMatrices.a)) +
          ρ (ReferenceCoefficientMatrices.a ^ 2)
            (F (act (rowS g) (ReferenceCoefficientMatrices.a ^ 2)))) := by
      simp only [rowS_mul, map_mul, Module.End.mul_apply, map_add]
    rw [e, h, map_zero]


open TernaryPoly.OrdinaryIncidenceChains in
/-- The cycle map `Φ_F` of a fiber system. -/
def cycleMapOf {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) : Cycles →ₗ[ℚ] E :=
  (TernaryPoly.OrdinaryApartmentEvaluation.relativeEvaluator (frameValues hF)).comp
    presentation.symm.toLinearMap

theorem cycleMapOf_frame {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) (g : IntegralGL) :
    cycleMapOf hF (frameCycle g) = ρ g (F (rowS g)) := by
  change TernaryPoly.OrdinaryApartmentEvaluation.relativeEvaluator (frameValues hF)
    (presentation.symm (presentation (TernaryPoly.OrdinaryRelativeChains.quotientMap
      (TernaryPoly.OrdinaryRelativeChains.triangle g)))) = _
  rw [LinearEquiv.symm_apply_apply, TernaryPoly.OrdinaryApartmentEvaluation.relativeEvaluator_triangle]
  rfl

theorem rowS_left_K (k : K) (g : IntegralGL) : rowS (k.val * g) = rowS g :=
  Subtype.ext (row_left_K k g)

open TernaryPoly.OrdinaryIncidenceChains in
/-- The equivariant cycle maps, as a `ℚ`-subspace of the linear maps. -/
def homK (ρ : Representation ℚ IntegralGL E) : Submodule ℚ (Cycles →ₗ[ℚ] E) where
  carrier := {Φ | ∀ (k : K) (z : Cycles), Φ (complex.cyclesAction k z) = ρ k.val (Φ z)}
  zero_mem' := by intro k z; simp
  add_mem' := by
    intro Φ Ψ hΦ hΨ k z
    simp only [LinearMap.add_apply, hΦ k z, hΨ k z, map_add]
  smul_mem' := by
    intro c Φ hΦ k z
    simp only [LinearMap.smul_apply, hΦ k z, map_smul]

theorem cycleMapOf_mem {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) :
    cycleMapOf hF ∈ homK ρ := by
  intro k z
  have he : (cycleMapOf hF).comp (TernaryPoly.OrdinaryIncidenceChains.complex.cyclesAction k) =
      (ρ k.val).comp (cycleMapOf hF) := by
    apply cycle_functional_ext
    intro g
    simp only [LinearMap.comp_apply, frameCycle_equivariant, cycleMapOf_frame, rowS_left_K,
      map_mul, Module.End.mul_apply]
  exact LinearMap.congr_fun he z


open TernaryPoly.OrdinaryIncidenceChains

/-- The fiber function of a linear map on cycles: `F_Φ(row g) = ρ(g)⁻¹ Φ(apartment of g)`. -/
def fiberOf (ρ : Representation ℚ IntegralGL E) (Φ : Cycles →ₗ[ℚ] E) :
    NonzeroCovector → E := fun r =>
  ρ (Classical.choose (act_surjective r))⁻¹ (Φ (frameCycle (Classical.choose (act_surjective r))))

theorem fiberOf_rowS {Φ : Cycles →ₗ[ℚ] E} (hΦ : Φ ∈ homK ρ) (g : IntegralGL) :
    fiberOf ρ Φ (rowS g) = ρ g⁻¹ (Φ (frameCycle g)) := by
  have hg' : rowS (Classical.choose (act_surjective (rowS g))) = rowS g :=
    Classical.choose_spec (act_surjective (rowS g))
  obtain ⟨k, hk⟩ := (rowS_eq_iff _ _).mp hg'
  change ρ (Classical.choose (act_surjective (rowS g)))⁻¹
    (Φ (frameCycle (Classical.choose (act_surjective (rowS g))))) = _
  generalize Classical.choose (act_surjective (rowS g)) = g' at hk
  subst hk
  rw [← frameCycle_equivariant, hΦ k, mul_inv_rev, rho_mul_apply, rho_inv_cancel']

theorem fiberOf_term {Φ : Cycles →ₗ[ℚ] E} (hΦ : Φ ∈ homK ρ) (g h : IntegralGL) :
    ρ h (fiberOf ρ Φ (act (rowS g) h)) = ρ g⁻¹ (Φ (frameCycle (g * h))) := by
  rw [← rowS_mul, fiberOf_rowS hΦ, mul_inv_rev, rho_mul_apply, rho_inv_cancel]

theorem fiberOf_mem {Φ : Cycles →ₗ[ℚ] E} (hΦ : Φ ∈ homK ρ) : IsFiberSystem ρ (fiberOf ρ Φ) := by
  constructor
  · intro s π r
    obtain ⟨g, rfl⟩ := act_surjective r
    rw [← rowS_mul, fiberOf_rowS hΦ, fiberOf_rowS hΦ, frameCycle_signedPerm, mul_inv_rev,
      rho_mul_apply]
    simp only [map_zsmul]
  · intro r
    obtain ⟨g, rfl⟩ := act_surjective r
    have e : normExpr ρ (fiberOf ρ Φ) (rowS g) = ρ g⁻¹ (Φ (frameCycle g)) +
        ρ g⁻¹ (Φ (frameCycle (g * ReferenceCoefficientMatrices.a))) +
        ρ g⁻¹ (Φ (frameCycle (g * ReferenceCoefficientMatrices.a ^ 2))) := by
      unfold normExpr
      rw [fiberOf_rowS hΦ, fiberOf_term hΦ, fiberOf_term hΦ]
    have h0 : Φ (frameCycle g) + Φ (frameCycle (g * ReferenceCoefficientMatrices.a)) +
        Φ (frameCycle (g * ReferenceCoefficientMatrices.a ^ 2)) = 0 := by
      rw [← map_add, ← map_add, OrdinaryFullAction.frameCycle_norm, map_zero]
    rw [e, ← map_add, ← map_add, h0, map_zero]

theorem cycleMapOf_fiberOf {Φ : Cycles →ₗ[ℚ] E} (hΦ : Φ ∈ homK ρ) :
    cycleMapOf (fiberOf_mem hΦ) = Φ := by
  apply cycle_functional_ext
  intro g
  rw [cycleMapOf_frame, fiberOf_rowS hΦ, rho_inv_cancel]

theorem fiberOf_cycleMapOf {F : NonzeroCovector → E} (hF : IsFiberSystem ρ F) :
    fiberOf ρ (cycleMapOf hF) = F := by
  funext r
  obtain ⟨g, rfl⟩ := act_surjective r
  rw [fiberOf_rowS (cycleMapOf_mem hF), cycleMapOf_frame, rho_inv_cancel']

/-- The cycle map of a member of `fiberSpace`. -/
def cycleMapOfMem (F : fiberSpace ρ) : Cycles →ₗ[ℚ] E := cycleMapOf ((mem_fiberSpace ρ).mp F.2)

theorem cycleMapOfMem_frame (F : fiberSpace ρ) (g : IntegralGL) :
    cycleMapOfMem F (frameCycle g) = ρ g (F.1 (rowS g)) :=
  cycleMapOf_frame _ g

/-- **Fiber model of the equivariant maps out of the Steinberg module.**  The linear equivalence
between the fiber functions (signed permutation relations and norm relation) and the
`K`-equivariant linear maps from the ordinary incidence cycles to `E`. -/
def fiberEquiv (ρ : Representation ℚ IntegralGL E) : fiberSpace ρ ≃ₗ[ℚ] homK ρ where
  toFun F := ⟨cycleMapOfMem F, cycleMapOf_mem _⟩
  invFun Φ := ⟨fiberOf ρ Φ.1, (mem_fiberSpace ρ).mpr (fiberOf_mem Φ.2)⟩
  map_add' F G := by
    apply Subtype.ext
    apply cycle_functional_ext
    intro g
    change cycleMapOfMem (F + G) (frameCycle g) = cycleMapOfMem F (frameCycle g) +
      cycleMapOfMem G (frameCycle g)
    rw [cycleMapOfMem_frame, cycleMapOfMem_frame, cycleMapOfMem_frame, ← map_add]
    rfl
  map_smul' c F := by
    apply Subtype.ext
    apply cycle_functional_ext
    intro g
    change cycleMapOfMem (c • F) (frameCycle g) = c • cycleMapOfMem F (frameCycle g)
    rw [cycleMapOfMem_frame, cycleMapOfMem_frame, ← map_smul]
    rfl
  left_inv F := Subtype.ext (fiberOf_cycleMapOf _)
  right_inv Φ := Subtype.ext (cycleMapOf_fiberOf Φ.2)

theorem fiberEquiv_frame (F : fiberSpace ρ) (g : IntegralGL) :
    (fiberEquiv ρ F).1 (frameCycle g) = ρ g (F.1 (rowS g)) :=
  cycleMapOfMem_frame F g

theorem fiberEquiv_symm_rowS (Φ : homK ρ) (g : IntegralGL) :
    ((fiberEquiv ρ).symm Φ).1 (rowS g) = ρ g⁻¹ (Φ.1 (frameCycle g)) :=
  fiberOf_rowS Φ.2 g

end Fibers

end TernaryPeriodPolynomials.Argument.FiberModel
