module

public import TernaryPeriodPolynomials.BoundaryComparison.LevelTransfer
public import TernaryPeriodPolynomials.ArithmeticCohomology.EisensteinGraph.InnerCuspidalArithmetic.LocalInner

@[expose] public section


/-!
# Presentation-free level descent of the locally inner classes, at every face

Paper: Lemma C.3 (`ar:lem:seed`),
 ("the finite reflection projection supplies the full-level statement").

In the homogeneous-cochain model of the face library, for a subgroup `M` of the level group that is
normalized by it and has finite relative index (`levelPrincipal N = Γ ∩ Γ(N)`):

* `locallyInnerAt`: the locally inner classes of `H²(Γ_F, ρ)` for an arbitrary level subgroup `level`
  (`locallyInnerClasses_eq`: for `level = rationalLevel` this is the face library's definition);
* `res_level_injective`: restriction `H²(Γ_x, ρ) → H²(Γ_x ∩ M, ρ)` is injective;
* `mem_locallyInnerAt_iff_res`: **a class of `H²(Γ_F, ρ)` is locally inner iff its restriction to
  `Γ_F ∩ M` is locally inner for the level `M`**, for every flag `F`: plane or line, good or bad, any
  rational cusp.  No splitting, no presentation of the stabilizer as a semidirect product and no
  coefficient comparison enters;
* `map_locallyInnerAt_eq`: **`𝒞(Γ) = 𝒞(M)^{invariants}`**: restriction maps the locally inner classes
  onto the classes of `H²(Γ_F ∩ M, ρ)` that are locally inner for `M` and invariant under conjugation by
  `Γ_F` (`LevelTransfer.invariantsH2`);
* `locallyInnerClasses_level_descent`, `map_locallyInnerClasses_eq`: the same for the face library's
  `locallyInnerClasses` and `M = Γ ∩ Γ(N)`.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous Matrix
open TernaryPeriodPolynomials.EisensteinGraph.InnerCuspidalArithmetic.Helpers
open TernaryPeriodPolynomials.Argument.LevelTransfer

noncomputable section

namespace TernaryPeriodPolynomials.Argument.SeedC3S4c

section LocallyInnerAt

variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)

theorem fixedPointLevel_edge_le_flag' (level : Subgroup RationalGL3) (side : Side) (edge : Edges)
    (flag : Flags side) (endpoint_eq : endpoint side edge = flag) :
    fixedPointLevel level edge ≤ fixedPointLevel level flag := by
  intro element membership
  refine ⟨membership.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  rw [← endpoint_eq, ← endpoint_smul, MulAction.mem_stabilizer_iff.mp membership.2]

/-- The locally inner classes of `H²(Γ_F, ρ)` for an arbitrary level subgroup `level`: the classes
vanishing on the stabilizer in `level` of every complete flag over `F`. -/
def locallyInnerAt (level : Subgroup RationalGL3) {side : Side} (flag : Flags side) :
    Submodule ℂ (H2 (fixedPointLevel level flag) ρ) :=
  ⨅ edge : {edge : Edges // endpoint side edge = flag},
    LinearMap.ker (resH2 ρ (fixedPointLevel_edge_le_flag' level side edge.val flag edge.property))

theorem locallyInnerClasses_eq (degree : ℕ) (character : RankOneCharacter) {side : Side}
    (flag : Flags side) :
    locallyInnerClasses degree character side flag =
      locallyInnerAt (rationalCoefficientComponent degree character) rationalLevel flag := rfl

section Descent

variable (M : Subgroup RationalGL3) (hM : M ≤ rationalLevel)
  (hMnorm : ∀ g ∈ rationalLevel, ∀ m ∈ M, g⁻¹ * m * g ∈ M)
  [M.IsFiniteRelIndex rationalLevel]

omit [M.IsFiniteRelIndex rationalLevel] in
include hM in
theorem fixedPointLevel_mono_level {X : Type} [MulAction RationalGL3 X] (x : X) :
    fixedPointLevel M x ≤ fixedPointLevel rationalLevel x :=
  fun _ hg => ⟨hM hg.1, hg.2⟩

omit hM [M.IsFiniteRelIndex rationalLevel] in
include hMnorm in
theorem fixedPointLevel_hnorm {X : Type} [MulAction RationalGL3 X] (x : X) :
    ∀ s ∈ fixedPointLevel rationalLevel x, ∀ n ∈ fixedPointLevel M x,
      s⁻¹ * n * s ∈ fixedPointLevel M x := by
  intro s hs n hn
  refine ⟨hMnorm s hs.1 n hn.1, ?_⟩
  apply MulAction.mem_stabilizer_iff.mpr
  have h1 : s • x = x := MulAction.mem_stabilizer_iff.mp hs.2
  have h2 : n • x = x := MulAction.mem_stabilizer_iff.mp hn.2
  rw [mul_smul, mul_smul, h1, h2, ← h1, ← mul_smul, inv_mul_cancel, one_smul]
  exact h1.symm ▸ rfl

include hM hMnorm in
/-- The restriction `H²(Γ_x, ρ) → H²(Γ_x ∩ M, ρ)` is injective for a normal finite-index `M`. -/
theorem res_level_injective {X : Type} [MulAction RationalGL3 X] (x : X) :
    Function.Injective (resH2 ρ (fixedPointLevel_mono_level M hM x)) := by
  have hfin : (M.subgroupOf (fixedPointLevel rationalLevel x)).FiniteIndex := by
    have : M.IsFiniteRelIndex (fixedPointLevel rationalLevel x) :=
      Subgroup.isFiniteRelIndex_of_le_right (H := M) (K := fixedPointLevel rationalLevel x)
        (L := rationalLevel) inf_le_left
    infer_instance
  have heq : (fixedPointLevel M x).subgroupOf (fixedPointLevel rationalLevel x) =
      M.subgroupOf (fixedPointLevel rationalLevel x) := by
    ext g
    exact ⟨fun h => h.1, fun h => ⟨h, g.2.2⟩⟩
  have hfin' : ((fixedPointLevel M x).subgroupOf (fixedPointLevel rationalLevel x)).FiniteIndex := by
    rw [heq]; exact hfin
  let _ : Fintype (↥(fixedPointLevel rationalLevel x) ⧸
      (fixedPointLevel M x).subgroupOf (fixedPointLevel rationalLevel x)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  exact resH2_injective ρ (fixedPointLevel_mono_level M hM x) (fixedPointLevel_hnorm M hMnorm x)

include hM hMnorm in
/-- **Presentation-free level descent of the locally inner classes.** For a normal finite-index
subgroup `M` of the level group and any flag `F` (plane or line, any cusp), a class of `H²(Γ_F, ρ)` is
locally inner iff its restriction to `Γ_F ∩ M` is locally inner for the level `M`. -/
theorem mem_locallyInnerAt_iff_res {side : Side} (flag : Flags side)
    (x : H2 (fixedPointLevel rationalLevel flag) ρ) :
    x ∈ locallyInnerAt ρ rationalLevel flag ↔
      resH2 ρ (fixedPointLevel_mono_level M hM flag) x ∈ locallyInnerAt ρ M flag := by
  simp only [locallyInnerAt, Submodule.mem_iInf, LinearMap.mem_ker]
  refine forall_congr' fun e => ?_
  have hc : resH2 ρ (fixedPointLevel_edge_le_flag' M side e.val flag e.property)
      (resH2 ρ (fixedPointLevel_mono_level M hM flag) x) =
      resH2 ρ (fixedPointLevel_mono_level M hM e.val)
        (resH2 ρ (fixedPointLevel_edge_le_flag' rationalLevel side e.val flag e.property) x) := by
    rw [resH2_comp, resH2_comp]
  rw [hc]
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact res_level_injective ρ M hM hMnorm e.val (h.trans (map_zero _).symm)

include hM hMnorm in
/-- **`𝒞(Γ) = 𝒞(M)^{invariants}`, presentation-free.**  Restriction maps the locally inner classes of
`H²(Γ_F, ρ)` onto the classes of `H²(Γ_F ∩ M, ρ)` that are locally inner for the level `M` and
invariant under the action of `Γ_F` by conjugation. -/
theorem map_locallyInnerAt_eq {side : Side} (flag : Flags side) :
    Submodule.map (resH2 ρ (fixedPointLevel_mono_level M hM flag))
        (locallyInnerAt ρ rationalLevel flag) =
      locallyInnerAt ρ M flag ⊓
        invariantsH2 ρ (fixedPointLevel_hnorm M hMnorm flag) := by
  have hfin : (M.subgroupOf (fixedPointLevel rationalLevel flag)).FiniteIndex := by
    have : M.IsFiniteRelIndex (fixedPointLevel rationalLevel flag) :=
      Subgroup.isFiniteRelIndex_of_le_right (H := M) (K := fixedPointLevel rationalLevel flag)
        (L := rationalLevel) inf_le_left
    infer_instance
  have heq : (fixedPointLevel M flag).subgroupOf (fixedPointLevel rationalLevel flag) =
      M.subgroupOf (fixedPointLevel rationalLevel flag) := by
    ext g
    exact ⟨fun h => h.1, fun h => ⟨h, g.2.2⟩⟩
  have hfin' : ((fixedPointLevel M flag).subgroupOf
      (fixedPointLevel rationalLevel flag)).FiniteIndex := by
    rw [heq]; exact hfin
  let _ : Fintype (↥(fixedPointLevel rationalLevel flag) ⧸
      (fixedPointLevel M flag).subgroupOf (fixedPointLevel rationalLevel flag)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(mem_locallyInnerAt_iff_res ρ M hM hMnorm flag x).mp hx, ?_⟩
    exact (mem_range_resH2_iff ρ (fixedPointLevel_mono_level M hM flag)
      (fixedPointLevel_hnorm M hMnorm flag) _).mp ⟨x, rfl⟩
  · rintro ⟨hy, hinv⟩
    obtain ⟨x, rfl⟩ := (mem_range_resH2_iff ρ (fixedPointLevel_mono_level M hM flag)
      (fixedPointLevel_hnorm M hMnorm flag) y).mpr hinv
    exact ⟨x, (mem_locallyInnerAt_iff_res ρ M hM hMnorm flag x).mpr hy, rfl⟩

end Descent

end LocallyInnerAt

section Principal

/-- The reduction modulo `N` on the arithmetic level. -/
def levelReduce (N : ℕ) : arithmeticLevel →* GL (Fin 3) (ZMod N) :=
  (GeneralLinearGroup.map (Int.castRingHom (ZMod N))).comp arithmeticLevel.subtype

/-- The principal congruence subgroup of level `N` of the paper's level group, inside `GL₃(ℚ)`:
`Γ ∩ Γ(N)`. -/
def levelPrincipal (N : ℕ) : Subgroup RationalGL3 := (levelReduce N).ker.map rationalInclusion

theorem levelPrincipal_le (N : ℕ) : levelPrincipal N ≤ rationalLevel := by
  rintro _ ⟨g, _, rfl⟩
  exact ⟨g, rfl⟩

theorem levelPrincipal_norm (N : ℕ) :
    ∀ g ∈ rationalLevel, ∀ m ∈ levelPrincipal N, g⁻¹ * m * g ∈ levelPrincipal N := by
  rintro _ ⟨a, rfl⟩ _ ⟨k, hk, rfl⟩
  refine ⟨a⁻¹ * k * a, ?_, by simp [map_mul, map_inv]⟩
  have := (levelReduce N).normal_ker.conj_mem k hk a⁻¹
  simpa using this

instance levelPrincipal_finiteRelIndex (N : ℕ) [NeZero N] :
    (levelPrincipal N).IsFiniteRelIndex rationalLevel := by
  have h1 : rationalLevel = (⊤ : Subgroup arithmeticLevel).map rationalInclusion := by
    rw [← MonoidHom.range_eq_map]; rfl
  have hinj : Function.Injective rationalInclusion := by
    intro a b h
    have h1 := congrArg (fun x : RationalGL3 => (x.val : Matrix (Fin 3) (Fin 3) ℚ)) h
    apply Subtype.ext
    apply Units.ext
    ext i j
    have := congrFun (congrFun h1 i) j
    simpa [rationalInclusion, GeneralLinearGroup.map_apply] using this
  rw [Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero, h1, levelPrincipal,
    Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
  exact Subgroup.FiniteIndex.index_ne_zero (H := (levelReduce N).ker)

end Principal

section Corollaries

variable (N : ℕ) [NeZero N]

/-- Restriction `H²(Γ_F) → H²(Γ_F ∩ (Γ ∩ Γ(N)))`. -/
abbrev resPrincipal {side : Side} (flag : Flags side) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ RationalGL3 V) :
    H2 (fixedPointLevel rationalLevel flag) ρ →ₗ[ℂ] H2 (fixedPointLevel (levelPrincipal N) flag) ρ :=
  resH2 ρ (fixedPointLevel_mono_level (levelPrincipal N) (levelPrincipal_le N) flag)

/-- **Level descent of the face library's locally inner classes to `Γ ∩ Γ(N)`.** -/
theorem locallyInnerClasses_level_descent (degree : ℕ) (character : RankOneCharacter) {side : Side}
    (flag : Flags side) (x : H2 (fixedPointLevel rationalLevel flag)
      (rationalCoefficientComponent degree character)) :
    x ∈ locallyInnerClasses degree character side flag ↔
      resPrincipal N flag (rationalCoefficientComponent degree character) x ∈
        locallyInnerAt (rationalCoefficientComponent degree character) (levelPrincipal N) flag :=
  mem_locallyInnerAt_iff_res _ (levelPrincipal N) (levelPrincipal_le N) (levelPrincipal_norm N) flag x

/-- **`𝒞(Γ) = 𝒞(Γ ∩ Γ(N))^{invariants}` for the face library's locally inner classes.** -/
theorem map_locallyInnerClasses_eq (degree : ℕ) (character : RankOneCharacter) {side : Side}
    (flag : Flags side) :
    Submodule.map (resPrincipal N flag (rationalCoefficientComponent degree character))
        (locallyInnerClasses degree character side flag) =
      locallyInnerAt (rationalCoefficientComponent degree character) (levelPrincipal N) flag ⊓
        invariantsH2 (rationalCoefficientComponent degree character)
          (fixedPointLevel_hnorm (levelPrincipal N) (levelPrincipal_norm N) flag) :=
  map_locallyInnerAt_eq _ (levelPrincipal N) (levelPrincipal_le N) (levelPrincipal_norm N) flag

end Corollaries

end TernaryPeriodPolynomials.Argument.SeedC3S4c
