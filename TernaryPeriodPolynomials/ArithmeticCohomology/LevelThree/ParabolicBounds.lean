module

public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.GammaOneThree
public import TernaryPeriodPolynomials.ArithmeticCohomology.LevelThree.SymFixed

@[expose] public section


/-!
# Dimension bounds for the level-three Levi cohomology

For `Sym^m(ℂ²) ⊗ det^e` (`m > 0`) and `k = m + 2`:

* `finrank_core_H1_le`: `dim H¹(Γ₁(3), Sym^m) ≤ 2⌊k/3⌋`;
* `finrank_core_parabolicH1_le`: `dim H¹_par(Γ₁(3), Sym^m) ≤ 2(⌊k/3⌋ - 1)`, where parabolic means
  trivial on the cusp stabilizers `⟨T⟩` and `⟨L⟩` (the Eichler–Shimura value `2 dim S_k(Γ₁(3))`);
* `finrank_level_H1_le`: the same bound as the first for the Levi `Γ₁'(3) = binaryArithmeticLevel`;
* `finrank_binaryParabolicH1_le`: Sol's parabolic subspace `binaryParabolicH1 degree` of the bad-line
  Levi cohomology has dimension `≤ 2(⌊(degree + 3)/3⌋ - 1)`;
* `finrank_innerBadLineClasses_le`: hence so has the space of inner bad-line classes
  `innerBadLineClasses degree` (`0 < degree`). For `degree = 1, 2` the bound is `0`, recovering Sol's
  low-degree vanishing uniformly.

The counts come from `TwoGenerator` (Mayer–Vietoris-type cocycle counting for `⟨T, L⟩` with
`(T L⁻¹)³ = 1`) and the fixed-space computations of `SymFixed`.

Original work by Claude Opus 5.5 (AxiomCode).
-/

noncomputable section

namespace TernaryPeriodPolynomials.LevelThree.ParabolicBounds

open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic
open Helpers ArithmeticGenerators LowDegreeParabolic
open TwoGenerator GammaOneThree SymFixed
open GeneralEisenstein Module Matrix

section Count

/-- `e(m) = #{a ≤ m : 3 ∣ m + a} = dim (Sym^m)^E`. -/
def ellipticCount (m : ℕ) : ℕ := ((Finset.range (m + 1)).filter (fun a => 3 ∣ m + a)).card

theorem ellipticCount_add_three (m : ℕ) : ellipticCount (m + 3) = ellipticCount m + 1 := by
  unfold ellipticCount
  have split : (Finset.range (m + 3 + 1)).filter (fun a => 3 ∣ m + 3 + a) =
      ((Finset.range (m + 1)).filter (fun a => 3 ∣ m + a)) ∪
        ((Finset.Ico (m + 1) (m + 4)).filter (fun a => 3 ∣ m + a)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    constructor
    · rintro ⟨ha, hd⟩
      have hd' : 3 ∣ m + a := by omega
      by_cases h : a < m + 1
      · exact Or.inl ⟨h, hd'⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hd'⟩
    · rintro (⟨ha, hd⟩ | ⟨⟨ha, hb⟩, hd⟩) <;> exact ⟨by omega, by omega⟩
  have disjoint : Disjoint ((Finset.range (m + 1)).filter (fun a => 3 ∣ m + a))
      ((Finset.Ico (m + 1) (m + 4)).filter (fun a => 3 ∣ m + a)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha hb
    omega
  have single : ((Finset.Ico (m + 1) (m + 4)).filter (fun a => 3 ∣ m + a)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨m + 1 + (m + 2) % 3, ?_⟩
    ext a
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨ha, hb⟩, hd⟩
      omega
    · rintro rfl
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [split, Finset.card_union_of_disjoint disjoint, single]

/-- `e(m) + 2⌊(m + 2)/3⌋ = m + 1`. -/
theorem ellipticCount_add (m : ℕ) : ellipticCount m + 2 * ((m + 2) / 3) = m + 1 := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases Nat.lt_or_ge m 3 with small | large
    · interval_cases m <;> decide
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have := ih k (by omega)
      rw [ellipticCount_add_three]
      omega

theorem card_fin_eq_ellipticCount (m : ℕ) :
    (Finset.univ.filter (fun a : Fin (m + 1) => 3 ∣ m + a.val)).card = ellipticCount m :=
  Spectral.ModularSymDimension.card_filter_fin (m + 1) (fun a => 3 ∣ m + a)

end Count

section Representations

/-- `Sym^m(ℂ²) ⊗ det^e` as a representation of `Γ₁'(3) = binaryArithmeticLevel`. -/
abbrev levelRep (m : ℕ) (e : ℤ) :
    Representation ℂ binaryArithmeticLevel (Binary.HomogeneousPoly m) :=
  (Binary.homogeneousAction m e).comp (binaryIntegralComplex.comp binaryArithmeticLevel.subtype)

/-- Its restriction to `Γ₁(3)`. -/
abbrev coreRep (m : ℕ) (e : ℤ) : Representation ℂ core (Binary.HomogeneousPoly m) :=
  (levelRep m e).comp core.subtype

theorem binaryArithmeticRepresentation_eq (degree : ℕ) :
    binaryArithmeticRepresentation degree = levelRep (degree + 1) 0 := rfl

theorem integral_upper : binaryIntegralComplex (upper 1).val = upperC 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryIntegralComplex, upper, upperC]

theorem integral_lower : binaryIntegralComplex (lower 1).val = lowerC 3 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [binaryIntegralComplex, lower, lowerC]

variable (m : ℕ) (e : ℤ)

theorem coreRep_T : coreRep m e coreT = Binary.homogeneousAction m e (upperC 1) := by
  change Binary.homogeneousAction m e (binaryIntegralComplex (upper 1).val) = _
  rw [integral_upper]

theorem coreRep_L : coreRep m e coreL = Binary.homogeneousAction m e (lowerC 3) := by
  change Binary.homogeneousAction m e (binaryIntegralComplex (lower 1).val) = _
  rw [integral_lower]

theorem coreRep_E : coreRep m e (coreT * coreL⁻¹) = Binary.homogeneousAction m e ellipticC := by
  change Binary.homogeneousAction m e
    (binaryIntegralComplex ((upper 1 * (lower 1)⁻¹ : binaryArithmeticLevel).val)) = _
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, integral_upper, integral_lower,
    upper_mul_lower_inv]

theorem fixed_T : fixed (coreRep m e) coreT = SymFixed.fixedSpace e (upperC 1) := by
  unfold fixed
  rw [coreRep_T]

theorem fixed_L : fixed (coreRep m e) coreL = SymFixed.fixedSpace e (lowerC 3) := by
  unfold fixed
  rw [coreRep_L]

theorem fixed_E : fixed (coreRep m e) (coreT * coreL⁻¹) = SymFixed.fixedSpace e ellipticC := by
  unfold fixed
  rw [coreRep_E]

theorem moved_T : moved (coreRep m e) coreT = SymFixed.movedSpace e (upperC 1) := by
  unfold moved
  rw [coreRep_T]

theorem moved_L : moved (coreRep m e) coreL = SymFixed.movedSpace e (lowerC 3) := by
  unfold moved
  rw [coreRep_L]

variable {m}

theorem core_invariants (positive : 0 < m) :
    fixed (coreRep m e) coreT ⊓ fixed (coreRep m e) coreL = ⊥ := by
  rw [fixed_T, fixed_L]
  exact fixed_upper_inf_fixed_lower e positive one_ne_zero three_ne_zero

theorem core_coinvariants (positive : 0 < m) :
    moved (coreRep m e) coreT ⊔ moved (coreRep m e) coreL = ⊤ := by
  rw [moved_T, moved_L]
  exact moved_upper_sup_moved_lower e positive one_ne_zero three_ne_zero

theorem finrank_fixed_core_E (m : ℕ) :
    finrank ℂ (fixed (coreRep m e) (coreT * coreL⁻¹)) = ellipticCount m := by
  rw [fixed_E, finrank_fixed_elliptic, card_fin_eq_ellipticCount]

theorem core_noInvariants (positive : 0 < m) (v : Binary.HomogeneousPoly m)
    (fixedAll : ∀ h ∈ core, levelRep m e h v = v) : v = 0 := by
  have member : v ∈ fixed (coreRep m e) coreT ⊓ fixed (coreRep m e) coreL :=
    ⟨(mem_fixed _).mpr (fixedAll _ coreT.property), (mem_fixed _).mpr (fixedAll _ coreL.property)⟩
  rw [core_invariants e positive, Submodule.mem_bot] at member
  exact member

end Representations

section Bounds

variable {m : ℕ} (e : ℤ)

/-- **`dim H¹(Γ₁(3), Sym^m ⊗ det^e) ≤ 2⌊(m + 2)/3⌋`** for `m > 0`. -/
theorem finrank_core_H1_le (positive : 0 < m) :
    finrank ℂ (CrossedH1 (coreRep m e)) ≤ 2 * ((m + 2) / 3) := by
  have h := finrank_H1_add_le (ρ := coreRep m e) core_closure core_elliptic_cube
  rw [core_invariants e positive, finrank_bot, finrank_fixed_core_E, finrank_sym] at h
  have count := ellipticCount_add m
  omega

/-- **`dim H¹_par(Γ₁(3), Sym^m ⊗ det^e) ≤ 2(⌊(m + 2)/3⌋ - 1)`** for `m > 0`. -/
theorem finrank_core_parabolicH1_le (positive : 0 < m) :
    finrank ℂ (parabolicH1 (coreRep m e) coreT coreL) + 2 ≤ 2 * ((m + 2) / 3) := by
  have h := finrank_parabolicH1_add_le (ρ := coreRep m e) core_closure core_elliptic_cube
    (core_invariants e positive) (core_coinvariants e positive)
  rw [fixed_T, fixed_L, finrank_fixed_upper e one_ne_zero, finrank_fixed_lower e three_ne_zero,
    finrank_fixed_core_E, finrank_sym] at h
  have count := ellipticCount_add m
  omega

theorem core_cocycles_finiteDimensional :
    FiniteDimensional ℂ (crossedCocycles (coreRep m e)) :=
  cocycles_finiteDimensional core_closure core_elliptic_cube

theorem core_H1_finiteDimensional : FiniteDimensional ℂ (CrossedH1 (coreRep m e)) := by
  have := core_cocycles_finiteDimensional (m := m) e
  infer_instance

/-- Restriction from the Levi `Γ₁'(3)` to `Γ₁(3)`. -/
abbrev restriction (m : ℕ) : CrossedH1 (levelRep m e) →ₗ[ℂ] CrossedH1 (coreRep m e) :=
  crossedPullbackH1 core.subtype (levelRep m e)

theorem restriction_injective (positive : 0 < m) : Function.Injective (restriction e m) :=
  core_pullback_injective (levelRep m e) (core_noInvariants e positive)

theorem level_H1_finiteDimensional (positive : 0 < m) :
    FiniteDimensional ℂ (CrossedH1 (levelRep m e)) := by
  have := core_H1_finiteDimensional (m := m) e
  exact Module.Finite.of_injective _ (restriction_injective e positive)

/-- **`dim H¹(Γ₁'(3), Sym^m ⊗ det^e) ≤ 2⌊(m + 2)/3⌋`** for `m > 0`. -/
theorem finrank_level_H1_le (positive : 0 < m) :
    finrank ℂ (CrossedH1 (levelRep m e)) ≤ 2 * ((m + 2) / 3) := by
  have := core_H1_finiteDimensional (m := m) e
  exact (LinearMap.finrank_le_finrank_of_injective (restriction_injective e positive)).trans
    (finrank_core_H1_le e positive)

end Bounds

section BadLine

/-- A parabolic class of the bad-line Levi restricts to a parabolic class of `Γ₁(3)`. -/
theorem restriction_parabolic (degree : ℕ) (x : CrossedH1 (binaryArithmeticRepresentation degree))
    (hx : x ∈ binaryParabolicH1 degree) :
    restriction 0 (degree + 1) x ∈ parabolicH1 (coreRep (degree + 1) 0) coreT coreL := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx' : (crossedBoundaries (binaryArithmeticRepresentation degree)).mkQ z ∈
      binaryParabolicH1 degree := hx
  refine ⟨crossedPullbackCocycles core.subtype (levelRep (degree + 1) 0) z, ⟨?_, ?_⟩, rfl⟩
  · obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' 1 (upper 1) upper_cusp
    exact ⟨p, hp.symm⟩
  · have membership : lower 1 ∈ binaryCuspLevel oppositeFrame := by
      rw [← inv_inv (lower 1), lower_inv]
      exact (binaryCuspLevel oppositeFrame).inv_mem lower_cusp
    obtain ⟨p, hp⟩ := parabolic_generator_primitive z hx' oppositeFrame (lower 1) membership
    exact ⟨p, hp.symm⟩

/-- **The parabolic bad-line Levi cohomology has dimension `≤ 2(⌊(degree + 3)/3⌋ - 1)`.** -/
theorem finrank_binaryParabolicH1_le (degree : ℕ) :
    finrank ℂ (binaryParabolicH1 degree) + 2 ≤ 2 * ((degree + 3) / 3) := by
  have positive : 0 < degree + 1 := Nat.succ_pos degree
  have := core_H1_finiteDimensional (m := degree + 1) 0
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 positive
  let f : binaryParabolicH1 degree →ₗ[ℂ] parabolicH1 (coreRep (degree + 1) 0) coreT coreL :=
    ((restriction 0 (degree + 1)).comp (binaryParabolicH1 degree).subtype).codRestrict _
      (fun x => restriction_parabolic degree x.val x.property)
  have injective : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact restriction_injective 0 positive (congrArg Subtype.val h)
  have le := LinearMap.finrank_le_finrank_of_injective injective
  have bound := finrank_core_parabolicH1_le (m := degree + 1) 0 positive
  omega

/-- **Inner bad-line classes: `dim ≤ 2(⌊(degree + 3)/3⌋ - 1)`** (`0 < degree`). The space injects
into `binaryParabolicH1 degree` (Sol's `innerBadLineParabolicMap_injective`). -/
theorem finrank_innerBadLineClasses_le (degree : ℕ) (positive : 0 < degree) :
    finrank ℂ (innerBadLineClasses degree) + 2 ≤ 2 * ((degree + 3) / 3) := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have le := LinearMap.finrank_le_finrank_of_injective
    (innerBadLineParabolicMap_injective degree positive)
  have bound := finrank_binaryParabolicH1_le degree
  omega

/-- In degrees one and two there are no inner bad-line classes. -/
theorem innerBadLineClasses_eq_bot_of_le_two (degree : ℕ) (positive : 0 < degree)
    (small : degree ≤ 2) : innerBadLineClasses degree = ⊥ := by
  have : FiniteDimensional ℂ (CrossedH1 (binaryArithmeticRepresentation degree)) :=
    level_H1_finiteDimensional 0 (Nat.succ_pos degree)
  have finite : FiniteDimensional ℂ (innerBadLineClasses degree) :=
    Module.Finite.of_injective _ (innerBadLineParabolicMap_injective degree positive)
  have bound := finrank_innerBadLineClasses_le degree positive
  have zero : finrank ℂ (innerBadLineClasses degree) = 0 := by
    interval_cases degree <;> omega
  exact Submodule.finrank_eq_zero.mp zero

end BadLine

end TernaryPeriodPolynomials.LevelThree.ParabolicBounds
