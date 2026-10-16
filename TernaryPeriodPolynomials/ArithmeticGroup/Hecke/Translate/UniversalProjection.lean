/-
  The projection onto the associate pair is *unconditional*: over a division ring
  every subspace has a complement (`Submodule.exists_isCompl`), so a linear map with
  `range = associatePair D` fixing the pair exists with no arithmetic input.
  Consequently the whole content of the target's existence clause is the
  commutation with the Hecke action.  For the canonical projection along a chosen
  complement this commutation is equivalent to invariance of *both* summands.
-/
module

public import TernaryPeriodPolynomials.ArithmeticCohomology.Defs
public import Mathlib.LinearAlgebra.Projection
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Insufficiency
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.Obstruction

@[expose] public section


open GeneralEisenstein


noncomputable section

namespace TernaryPeriodPolynomials.HeckeTranslate.UniversalProjection


/-! ### Linear algebra over an abstract module

The statements below are about a subspace `A` of a `ℂ`-module `V` and a family `H` of
endomorphisms.  They are proved for an arbitrary module so that the elaborator never has to
unify instances on the concrete (cohomological) module of boundary coordinates. -/

section Generic

variable {V ι : Type*} [AddCommGroup V] [Module ℂ V]

/-- `p` has range `A`, fixes `A`, and commutes with every `H t`. -/
private def IsProj (A : Submodule ℂ V) (H : ι → Module.End ℂ V) (p : Module.End ℂ V) : Prop :=
  LinearMap.range p = A ∧ (∀ x ∈ A, p x = x) ∧ ∀ t, p.comp (H t) = (H t).comp p

variable {A : Submodule ℂ V} {H : ι → Module.End ℂ V}

private theorem exists_projection_onto (A : Submodule ℂ V) :
    ∃ p : Module.End ℂ V, LinearMap.range p = A ∧ ∀ x ∈ A, p x = x := by
  classical
  obtain ⟨complement, hcompl⟩ := Submodule.exists_isCompl A
  exact ⟨A.projection complement hcompl, Submodule.range_projection hcompl,
    fun _ hx => Submodule.projection_apply_of_mem_left hcompl hx⟩

private theorem projection_comp_iff {B : Submodule ℂ V} (h : IsCompl A B)
    (operator : Module.End ℂ V) :
    (A.projection B h).comp operator = operator.comp (A.projection B h) ↔
      (∀ x ∈ A, operator x ∈ A) ∧ (∀ x ∈ B, operator x ∈ B) := by
  constructor
  · intro hcomp
    refine ⟨?_, ?_⟩
    · intro x hx
      have h' := LinearMap.congr_fun hcomp x
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        Submodule.projection_apply_of_mem_left h hx] at h'
      exact h' ▸ Submodule.projection_apply_mem h (operator x)
    · intro x hx
      have h' := LinearMap.congr_fun hcomp x
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        Submodule.projection_apply_of_mem_right h hx, map_zero] at h'
      exact (Submodule.projection_apply_eq_zero_iff h).mp h'
  · rintro ⟨hpair, hcomplement⟩
    apply LinearMap.ext
    intro x
    have hx : x = A.projection B h x + (x - A.projection B h x) := by abel
    have hpx : A.projection B h x ∈ A := Submodule.projection_apply_mem h x
    have hqx : x - A.projection B h x ∈ B := Submodule.sub_projection_mem h x
    have key : operator x =
        operator (A.projection B h x) + operator (x - A.projection B h x) := by
      rw [← map_add]
      exact congrArg operator hx
    rw [LinearMap.comp_apply, LinearMap.comp_apply, key, map_add,
      Submodule.projection_apply_of_mem_left h (hpair _ hpx),
      Submodule.projection_apply_of_mem_right h (hcomplement _ hqx), add_zero]

private theorem IsProj.mem_range {p : Module.End ℂ V} (hp : IsProj A H p) (x : V) : p x ∈ A :=
  hp.1 ▸ LinearMap.mem_range_self p x

private theorem isCompl_ker_of_fix {p : Module.End ℂ V} (hrange : LinearMap.range p = A)
    (hfix : ∀ x ∈ A, p x = x) : IsCompl A (LinearMap.ker p) := by
  rw [← hrange]
  exact LinearMap.IsIdempotentElem.isCompl
    (LinearMap.ext fun x => hfix (p x) (hrange ▸ LinearMap.mem_range_self p x))

private theorem IsProj.isCompl_ker {p : Module.End ℂ V} (hp : IsProj A H p) :
    IsCompl A (LinearMap.ker p) :=
  isCompl_ker_of_fix hp.1 hp.2.1

private theorem IsProj.stable {p : Module.End ℂ V} (hp : IsProj A H p) (t : ι) :
    ∀ x ∈ A, H t x ∈ A := by
  intro x hx
  have h := LinearMap.congr_fun (hp.2.2 t) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hp.2.1 x hx] at h
  have hmem := hp.mem_range (H t x)
  rwa [h] at hmem

private theorem IsProj.ker_invariant {p : Module.End ℂ V} (hp : IsProj A H p) (t : ι) :
    ∀ x ∈ LinearMap.ker p, H t x ∈ LinearMap.ker p := by
  intro x hx
  have h := LinearMap.congr_fun (hp.2.2 t) x
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero] at h
  exact h

private theorem isProj_projection {B : Submodule ℂ V} (h : IsCompl A B)
    (hstab : ∀ t, ∀ x ∈ A, H t x ∈ A) (hinv : ∀ t, ∀ x ∈ B, H t x ∈ B) :
    IsProj A H (A.projection B h) :=
  ⟨Submodule.range_projection h, fun _ hx => Submodule.projection_apply_of_mem_left h hx,
    fun t => (projection_comp_iff h (H t)).mpr ⟨hstab t, hinv t⟩⟩

private theorem exists_isProj_iff_exists_invariant_complement :
    (∃ p : Module.End ℂ V, IsProj A H p) ↔
      (∀ t, ∀ x ∈ A, H t x ∈ A) ∧
      ∃ S' : Submodule ℂ V, IsCompl A S' ∧ ∀ t, ∀ x ∈ S', H t x ∈ S' := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨hp.stable, p.ker, hp.isCompl_ker, hp.ker_invariant⟩
  · rintro ⟨hstable, S', hcompl, hinv⟩
    exact ⟨A.projection S' hcompl, isProj_projection hcompl hstable hinv⟩

private theorem eq_projection_of_ker {p : Module.End ℂ V}
    (hcompl : IsCompl A (LinearMap.ker p))
    (hrange : LinearMap.range p = A) (hfix : ∀ x ∈ A, p x = x) :
    p = A.projection (LinearMap.ker p) hcompl := by
  apply LinearMap.ext
  intro x
  have hmemA : p x ∈ A := hrange ▸ LinearMap.mem_range_self p x
  have hmemK : x - p x ∈ LinearMap.ker p := by
    rw [LinearMap.mem_ker, map_sub, hfix (p x) hmemA, sub_self]
  have hdecomp : x = p x + (x - p x) := by abel
  conv_rhs => rw [hdecomp]
  rw [map_add, Submodule.projection_apply_of_mem_left hcompl hmemA,
    Submodule.projection_apply_of_mem_right hcompl hmemK, add_zero]

private theorem eq_of_ker_eq_of_fix {p p' : Module.End ℂ V}
    (hrange : LinearMap.range p = A) (hfix : ∀ x ∈ A, p x = x)
    (hfix' : ∀ x ∈ A, p' x = x)
    (hker : LinearMap.ker p = LinearMap.ker p') : p = p' := by
  have hcompl : IsCompl A (LinearMap.ker p) := isCompl_ker_of_fix hrange hfix
  apply LinearMap.ext
  intro x
  have hx : x ∈ A ⊔ LinearMap.ker p := by rw [hcompl.sup_eq_top]; trivial
  obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp hx
  have hk' : k ∈ LinearMap.ker p' := by rw [← hker]; exact hk
  rw [← hak, map_add, map_add, hfix a ha, hfix' a ha, LinearMap.mem_ker.mp hk,
    LinearMap.mem_ker.mp hk']

private theorem IsProj.unique_of_unique_complement
    (huniq : ∀ S₁ S₂ : Submodule ℂ V,
      (IsCompl A S₁ ∧ (∀ t, ∀ x ∈ S₁, H t x ∈ S₁)) →
      (IsCompl A S₂ ∧ (∀ t, ∀ x ∈ S₂, H t x ∈ S₂)) → S₁ = S₂)
    {S₀ : Submodule ℂ V} (hS₀ : IsCompl A S₀ ∧ (∀ t, ∀ x ∈ S₀, H t x ∈ S₀))
    {p p' : Module.End ℂ V} (hp : IsProj A H p) (hp' : IsProj A H p') : p = p' := by
  have key : ∀ q : Module.End ℂ V, IsProj A H q → LinearMap.ker q = S₀ := fun q hq =>
    huniq _ _ ⟨hq.isCompl_ker, hq.ker_invariant⟩ hS₀
  exact eq_of_ker_eq_of_fix hp.1 hp.2.1 hp'.2.1 (by rw [key p hp, key p' hp'])

private theorem projection_congr {S₁ S₂ : Submodule ℂ V} (h : S₁ = S₂)
    (h₁ : IsCompl A S₁) (h₂ : IsCompl A S₂) : A.projection S₁ h₁ = A.projection S₂ h₂ := by
  subst h
  rfl

private theorem unique_complement_of_unique_isProj
    (hstab : ∀ t, ∀ x ∈ A, H t x ∈ A)
    (huniq : ∀ p p' : Module.End ℂ V, IsProj A H p → IsProj A H p' → p = p')
    {S₁ S₂ : Submodule ℂ V}
    (h₁ : IsCompl A S₁ ∧ (∀ t, ∀ x ∈ S₁, H t x ∈ S₁))
    (h₂ : IsCompl A S₂ ∧ (∀ t, ∀ x ∈ S₂, H t x ∈ S₂)) : S₁ = S₂ := by
  have heq : A.projection S₁ h₁.1 = A.projection S₂ h₂.1 :=
    huniq _ _ (isProj_projection h₁.1 hstab h₁.2) (isProj_projection h₂.1 hstab h₂.2)
  rw [← Submodule.ker_projection h₁.1, heq, Submodule.ker_projection h₂.1]

private theorem existsUnique_isProj_iff_existsUnique_invariant_complement :
    (∃ p : Module.End ℂ V, IsProj A H p ∧ ∀ p', IsProj A H p' → p' = p) ↔
      (∀ t, ∀ x ∈ A, H t x ∈ A) ∧
      ∃ S' : Submodule ℂ V,
        (IsCompl A S' ∧ (∀ t, ∀ x ∈ S', H t x ∈ S')) ∧
        ∀ S'' : Submodule ℂ V,
          (IsCompl A S'' ∧ (∀ t, ∀ x ∈ S'', H t x ∈ S'')) → S'' = S' := by
  constructor
  · rintro ⟨p, hp, huniq⟩
    refine ⟨hp.stable, p.ker, ⟨hp.isCompl_ker, hp.ker_invariant⟩, fun S'' hS'' => ?_⟩
    have heq := huniq _ (isProj_projection hS''.1 hp.stable hS''.2)
    rw [← Submodule.ker_projection hS''.1, heq]
  · rintro ⟨hstab, S', hS', huniqS⟩
    refine ⟨A.projection S' hS'.1, isProj_projection hS'.1 hstab hS'.2, ?_⟩
    intro p' hp'
    have hker : LinearMap.ker p' = S' := huniqS _ ⟨hp'.isCompl_ker, hp'.ker_invariant⟩
    rw [eq_projection_of_ker hp'.isCompl_ker hp'.1 hp'.2.1, projection_congr hker _ hS'.1]

private theorem stable_of_scalar (h : ∀ t, ∃ c : ℂ, H t = c • LinearMap.id) :
    ∀ t, ∀ x ∈ A, H t x ∈ A := by
  intro t x hx
  obtain ⟨c, hc⟩ := h t
  rw [hc, LinearMap.smul_apply, LinearMap.id_apply]
  exact A.smul_mem c hx

private theorem exists_isProj_of_scalar (h : ∀ t, ∃ c : ℂ, H t = c • LinearMap.id) :
    ∃ p : Module.End ℂ V, IsProj A H p := by
  obtain ⟨p, hp1, hp2⟩ := exists_projection_onto A
  refine ⟨p, hp1, hp2, ?_⟩
  intro t
  obtain ⟨c, hc⟩ := h t
  rw [hc, LinearMap.comp_smul, LinearMap.comp_id, LinearMap.smul_comp, LinearMap.id_comp]

private theorem exists_isProj_of_semisimple_kernel (S : Module.End ℂ V)
    (hcomm : ∀ t, S.comp (H t) = (H t).comp S)
    (hker : LinearMap.ker S = A) (hcompl : IsCompl (LinearMap.ker S) (LinearMap.range S)) :
    ∃ p : Module.End ℂ V, IsProj A H p := by
  have hstab : ∀ t, ∀ x ∈ A, H t x ∈ A := by
    intro t x hx
    have hSx : S x = 0 := LinearMap.mem_ker.mp (hker.symm ▸ hx)
    rw [← hker, LinearMap.mem_ker]
    have h := LinearMap.congr_fun (hcomm t) x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hSx, map_zero] at h
    exact h
  have hinv : ∀ t, ∀ x ∈ LinearMap.range S, H t x ∈ LinearMap.range S := by
    intro t x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨H t y, LinearMap.congr_fun (hcomm t) y⟩
  have hcomplA : IsCompl A (LinearMap.range S) := by
    rw [← hker]
    exact hcompl
  exact ⟨A.projection (LinearMap.range S) hcomplA, isProj_projection hcomplA hstab hinv⟩

private theorem exists_idempotent_kernel_of_isProj {p : Module.End ℂ V} (hp : IsProj A H p) :
    IsIdempotentElem (LinearMap.id - p) ∧
      (∀ t, (LinearMap.id - p).comp (H t) = (H t).comp (LinearMap.id - p)) ∧
      LinearMap.ker (LinearMap.id - p) = A := by
  have hp2x : ∀ x, p (p x) = p x := fun x => hp.2.1 (p x) (hp.mem_range x)
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    rw [Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hp2x x]
    abel
  · intro t
    have hpt : ∀ x, p (H t x) = H t (p x) := fun x => LinearMap.congr_fun (hp.2.2 t) x
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hpt x]
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at hx
      have hx' : x = p x := sub_eq_zero.mp hx
      rw [hx']
      exact hp.mem_range x
    · intro x hx
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hp.2.1 x hx, sub_self]

private theorem isProj_one_sub {S : Module.End ℂ V} (hidem : IsIdempotentElem S)
    (hcomm : ∀ t, S.comp (H t) = (H t).comp S) (hker : LinearMap.ker S = A) :
    IsProj A H (LinearMap.id - S) := by
  have hS2x : ∀ x, S (S x) = S x := fun x => LinearMap.congr_fun hidem x
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨y, rfl⟩ := hx
      rw [← hker, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
        hS2x y, sub_self]
    · intro x hx
      have hx' : x ∈ LinearMap.ker S := hker.symm ▸ hx
      refine ⟨x, ?_⟩
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.mem_ker.mp hx', sub_zero]
  · intro x hx
    have hx' : x ∈ LinearMap.ker S := hker.symm ▸ hx
    rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.mem_ker.mp hx', sub_zero]
  · intro t
    have hSt : ∀ x, S (H t x) = H t (S x) := fun x => LinearMap.congr_fun (hcomm t) x
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, hSt x]

private theorem existsUnique_isProj_iff_existsUnique_idempotent_kernel :
    (∃ p : Module.End ℂ V, IsProj A H p ∧ ∀ p', IsProj A H p' → p' = p) ↔
      ∃ S : Module.End ℂ V,
        (IsIdempotentElem S ∧ (∀ t, S.comp (H t) = (H t).comp S) ∧ LinearMap.ker S = A) ∧
        ∀ S' : Module.End ℂ V,
          (IsIdempotentElem S' ∧ (∀ t, S'.comp (H t) = (H t).comp S') ∧
            LinearMap.ker S' = A) → S' = S := by
  constructor
  · rintro ⟨p, hp, huniq⟩
    refine ⟨LinearMap.id - p, exists_idempotent_kernel_of_isProj hp, ?_⟩
    intro S' hS'
    have e : LinearMap.id - S' = p := huniq _ (isProj_one_sub hS'.1 hS'.2.1 hS'.2.2)
    rw [← e]
    abel
  · rintro ⟨S, hS, huniqS⟩
    refine ⟨LinearMap.id - S, isProj_one_sub hS.1 hS.2.1 hS.2.2, ?_⟩
    intro p' hp'
    have heq : LinearMap.id - p' = S := huniqS _ (exists_idempotent_kernel_of_isProj hp')
    rw [← heq]
    abel

private theorem exists_isProj_iff_exists_commuting :
    (∃ p : Module.End ℂ V, IsProj A H p) ↔
      ∃ p : Module.End ℂ V, LinearMap.range p = A ∧ (∀ x ∈ A, p x = x) ∧
        ∀ t, p.comp (H t) = (H t).comp p :=
  Iff.rfl

private theorem exists_isProj_iff_exists_idempotent_kernel :
    (∃ p : Module.End ℂ V, IsProj A H p) ↔
      ∃ S : Module.End ℂ V, IsIdempotentElem S ∧
        (∀ t, S.comp (H t) = (H t).comp S) ∧ LinearMap.ker S = A := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨LinearMap.id - p, exists_idempotent_kernel_of_isProj hp⟩
  · rintro ⟨S, hidem, hcomm, hker⟩
    exact ⟨LinearMap.id - S, isProj_one_sub hidem hcomm hker⟩

end Generic


variable {n : ℕ} (D : InducingData n)

/-- **A projection onto the associate pair always exists.**  Its range is the pair
and it fixes the pair.  Only its commutation with the Hecke action is at stake. -/
theorem exists_projection_onto_associatePair :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range p = associatePair D ∧ ∀ x ∈ associatePair D, p x = x :=
  exists_projection_onto (associatePair D)

/-- The projection onto the associate pair along an explicit complement. -/
def associateProjection (complement : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) complement) :
    Module.End ℂ (BoundaryCoordinates n D.chi) :=
  (associatePair D).projection complement hcompl

theorem associateProjection_range (complement : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) complement) :
    LinearMap.range (associateProjection D complement hcompl) = associatePair D :=
  Submodule.range_projection hcompl

theorem associateProjection_fixes (complement : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) complement) :
    ∀ x ∈ associatePair D, associateProjection D complement hcompl x = x :=
  fun _ hx => Submodule.projection_apply_of_mem_left hcompl hx

variable {D}

/-- **Commutation criterion.**  For the projection onto the associate pair along a
complement, commuting with an operator is exactly invariance of *both* the pair and
its complement under that operator. -/
theorem associateProjection_comp_iff (complement : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) complement)
    (operator : Module.End ℂ (BoundaryCoordinates n D.chi)) :
    (associateProjection D complement hcompl).comp operator =
        operator.comp (associateProjection D complement hcompl) ↔
      (∀ x ∈ associatePair D, operator x ∈ associatePair D) ∧
      (∀ x ∈ complement, operator x ∈ complement) :=
  projection_comp_iff hcompl operator

/-- The target's existence clause, restated: it is exactly the existence of *some*
projection onto the associate pair that commutes with the whole Hecke action
(existence of such a projection being otherwise automatic). -/
theorem exists_isotypicalProjection_iff_exists_commuting_projection
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p) ↔
      ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
        LinearMap.range p = associatePair D ∧
        (∀ x ∈ associatePair D, p x = x) ∧
        ∀ t, p.comp (pairHecke D T t) = (pairHecke D T t).comp p :=
  exists_isProj_iff_exists_commuting (A := associatePair D) (H := pairHecke D T)


/-- **Existence of the isotypical projection is exactly the existence of a
Hecke-invariant complement of the associate pair** (the pair's own invariance
being forced).  This is the whole arithmetic content of the constructor: the
Harder--Raghunram associate-pair splitting. -/
theorem exists_isotypicalProjection_iff_exists_invariant_complement
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p) ↔
      (∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D) ∧
      ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
        IsCompl (associatePair D) S' ∧
        ∀ t, ∀ x ∈ S', pairHecke D T t x ∈ S' :=
  exists_isProj_iff_exists_invariant_complement (A := associatePair D) (H := pairHecke D T)


/-- **Capstone without the level-normaliser hypothesis.**  The two arithmetic
inputs isolated by the reductions — Hecke-stability of the associate pair and a
Hecke-invariant complement — plus the multiplicity-one vanishing `Q = 0` yield the
exact conclusion of the target. -/
theorem existsUnique_isotypicalProjection_of_split
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (hstable : ∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D)
    (hcompl : ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
      IsCompl (associatePair D) S' ∧
      ∀ t, ∀ x ∈ S', pairHecke D T t x ∈ S')
    (hQ : ∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
      LinearMap.range q ≤ associatePair D →
      (∀ x ∈ associatePair D, q x = 0) →
      (∀ t, q.comp (pairHecke D T t) = (pairHecke D T t).comp q) → q = 0) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D T p ∧
      ∀ p', IsIsotypicalProjection D T p' → p' = p := by
  have hex : ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p :=
    (exists_isotypicalProjection_iff_exists_invariant_complement T).2 ⟨hstable, hcompl⟩
  exact (TernaryPeriodPolynomials.HeckeTranslate.isotypical_unique_iff (T := T) hex).2 hQ


/-- The kernel of the projection onto the associate pair along a complement is that
complement (this makes `p ↦ ker p` a bijection from projections onto the pair to
complements of the pair). -/
theorem associateProjection_ker (complement : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) complement) :
    LinearMap.ker (associateProjection D complement hcompl) = complement :=
  Submodule.ker_projection hcompl

/-- A map with the associate pair as range that fixes the pair is the projection
onto the pair along its own kernel. -/
theorem eq_associateProjection_of_ker (p : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hcompl : IsCompl (associatePair D) (LinearMap.ker p))
    (hrange : LinearMap.range p = associatePair D)
    (hfix : ∀ x ∈ associatePair D, p x = x) :
    p = associateProjection D (LinearMap.ker p) hcompl :=
  eq_projection_of_ker hcompl hrange hfix


/-- Two maps with the associate pair as range that fix the pair and have the same
kernel are equal: the map is recovered from its (range, kernel). -/
theorem eq_of_ker_eq {p p' : Module.End ℂ (BoundaryCoordinates n D.chi)}
    (hrange : LinearMap.range p = associatePair D) (hfix : ∀ x ∈ associatePair D, p x = x)
    (_hrange' : LinearMap.range p' = associatePair D) (hfix' : ∀ x ∈ associatePair D, p' x = x)
    (hker : LinearMap.ker p = LinearMap.ker p') : p = p' :=
  eq_of_ker_eq_of_fix hrange hfix hfix' hker


/-- A unique Hecke-invariant complement yields a unique isotypical projection:
`p ↦ LinearMap.ker p` is a bijection from isotypical projections to Hecke-invariant
complements of the associate pair. -/
theorem unique_projection_of_unique_complement
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (huniq : ∀ S₁ S₂ : Submodule ℂ (BoundaryCoordinates n D.chi),
      (IsCompl (associatePair D) S₁ ∧ (∀ t, ∀ x ∈ S₁, pairHecke D T t x ∈ S₁)) →
      (IsCompl (associatePair D) S₂ ∧ (∀ t, ∀ x ∈ S₂, pairHecke D T t x ∈ S₂)) →
      S₁ = S₂)
    (S₀ : Submodule ℂ (BoundaryCoordinates n D.chi))
    (hS₀ : IsCompl (associatePair D) S₀ ∧ (∀ t, ∀ x ∈ S₀, pairHecke D T t x ∈ S₀))
    (p p' : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hp : IsIsotypicalProjection D T p) (hp' : IsIsotypicalProjection D T p') : p = p' :=
  IsProj.unique_of_unique_complement (A := associatePair D) (H := pairHecke D T) huniq hS₀ hp hp'


/-- The kernel of an isotypical projection is a Hecke-invariant complement of the
associate pair. -/
theorem isotypical_ker_invariant
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    {p : Module.End ℂ (BoundaryCoordinates n D.chi)} (hp : IsIsotypicalProjection D T p) :
    IsCompl (associatePair D) (LinearMap.ker p) ∧
      (∀ t, ∀ x ∈ LinearMap.ker p, pairHecke D T t x ∈ LinearMap.ker p) :=
  ⟨IsProj.isCompl_ker (A := associatePair D) (H := pairHecke D T) hp,
    IsProj.ker_invariant (A := associatePair D) (H := pairHecke D T) hp⟩

/-- The projection onto the associate pair along a Hecke-invariant complement is
isotypical (the backward half of the bijection). -/
theorem associateProjection_isotypical
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    {S' : Submodule ℂ (BoundaryCoordinates n D.chi)} (hcompl : IsCompl (associatePair D) S')
    (hstab : ∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D)
    (hinv : ∀ t, ∀ x ∈ S', pairHecke D T t x ∈ S') :
    IsIsotypicalProjection D T (associateProjection D S' hcompl) :=
  isProj_projection (A := associatePair D) (H := pairHecke D T) hcompl hstab hinv


/-- Conversely, a unique isotypical projection forces a unique Hecke-invariant
complement: `p ↦ ker p` is injective on isotypical projections. -/
theorem unique_complement_of_unique_projection
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (hstab : ∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D)
    (huniq : ∀ p p' : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIsotypicalProjection D T p → IsIsotypicalProjection D T p' → p = p')
    {S₁ S₂ : Submodule ℂ (BoundaryCoordinates n D.chi)}
    (h₁ : IsCompl (associatePair D) S₁ ∧ (∀ t, ∀ x ∈ S₁, pairHecke D T t x ∈ S₁))
    (h₂ : IsCompl (associatePair D) S₂ ∧ (∀ t, ∀ x ∈ S₂, pairHecke D T t x ∈ S₂)) :
    S₁ = S₂ :=
  unique_complement_of_unique_isProj (A := associatePair D) (H := pairHecke D T)
    hstab huniq h₁ h₂


/-- The projection along a complement depends only on the complement. -/
theorem associateProjection_congr {S₁ S₂ : Submodule ℂ (BoundaryCoordinates n D.chi)}
    (h : S₁ = S₂) (h₁ : IsCompl (associatePair D) S₁) (h₂ : IsCompl (associatePair D) S₂) :
    associateProjection D S₁ h₁ = associateProjection D S₂ h₂ :=
  projection_congr h h₁ h₂

/-- **The target's uniqueness clause is exactly uniqueness of the Hecke-invariant
complement.**  An isotypical projection exists uniquely iff the associate pair is
Hecke-stable and its Hecke-invariant complement is unique. -/
theorem existsUnique_isotypicalProjection_iff_existsUnique_invariant_complement
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
        IsIsotypicalProjection D T p ∧
        ∀ p', IsIsotypicalProjection D T p' → p' = p) ↔
      (∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D) ∧
      ∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
        (IsCompl (associatePair D) S' ∧
          (∀ t, ∀ x ∈ S', pairHecke D T t x ∈ S')) ∧
        ∀ S'' : Submodule ℂ (BoundaryCoordinates n D.chi),
          (IsCompl (associatePair D) S'' ∧
            (∀ t, ∀ x ∈ S'', pairHecke D T t x ∈ S'')) → S'' = S' :=
  existsUnique_isProj_iff_existsUnique_invariant_complement (A := associatePair D)
    (H := pairHecke D T)


/-- **Consistency of the two formulations of uniqueness.**  Given that some
isotypical projection exists, its uniqueness is equivalent both to `Q = 0` (the
multiplicity-one input, `TernaryPeriodPolynomials.HeckeTranslate.isotypical_unique_iff`) and to the uniqueness of
the Hecke-invariant complement. -/
theorem unique_invariant_complement_iff_Q_zero
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (hex : ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p) :
    (∃ S' : Submodule ℂ (BoundaryCoordinates n D.chi),
        (IsCompl (associatePair D) S' ∧
          (∀ t, ∀ x ∈ S', pairHecke D T t x ∈ S')) ∧
        ∀ S'' : Submodule ℂ (BoundaryCoordinates n D.chi),
          (IsCompl (associatePair D) S'' ∧
            (∀ t, ∀ x ∈ S'', pairHecke D T t x ∈ S'')) → S'' = S')
      ↔ (∀ q : Module.End ℂ (BoundaryCoordinates n D.chi),
        LinearMap.range q ≤ associatePair D →
        (∀ x ∈ associatePair D, q x = 0) →
        (∀ t, q.comp (pairHecke D T t) = (pairHecke D T t).comp q) → q = 0) := by
  have hstab : ∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D := by
    obtain ⟨p, hp⟩ := hex
    intro t
    exact TernaryPeriodPolynomials.HeckeTranslate.Obstruction.projector_forces_invariance hp t
  have hiff := existsUnique_isotypicalProjection_iff_existsUnique_invariant_complement T
  have hQ := TernaryPeriodPolynomials.HeckeTranslate.isotypical_unique_iff (T := T) hex
  constructor
  · intro hcomp
    exact hQ.mp (hiff.mpr ⟨hstab, hcomp⟩)
  · intro hQzero
    exact (hiff.mp (hQ.mpr hQzero)).2


/-- If every Hecke operator is a scalar, the associate pair is Hecke-stable. -/
theorem associatePair_hecke_stable_of_scalar_hecke
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (h : ∀ t, ∃ c : ℂ, pairHecke D T t = c • LinearMap.id) :
    ∀ t, ∀ x ∈ associatePair D, pairHecke D T t x ∈ associatePair D :=
  stable_of_scalar (A := associatePair D) (H := pairHecke D T) h

/-- If every Hecke operator is a scalar, an isotypical projection exists (any
projection onto the associate pair commutes with it). -/
theorem exists_isotypicalProjection_of_scalar_hecke
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (h : ∀ t, ∃ c : ℂ, pairHecke D T t = c • LinearMap.id) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p :=
  exists_isProj_of_scalar (A := associatePair D) (H := pairHecke D T) h


/-- **Existence from a semisimple spectral operator.**  If some operator `S` on the
boundary coordinates commutes with the whole Hecke action, has the associate pair as
kernel, and has `IsCompl (ker S) (range S)` (the semisimplicity condition), then an
isotypical projection exists: `range S` is a Hecke-invariant complement of the pair.
This is the exact form of the Harder–Raghunram spectral splitting needed for the
existence clause. -/
theorem exists_isotypicalProjection_of_semisimple_kernel
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (S : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hcomm : ∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S)
    (hker : LinearMap.ker S = associatePair D)
    (hcompl : IsCompl (LinearMap.ker S) (LinearMap.range S)) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p :=
  exists_isProj_of_semisimple_kernel (A := associatePair D) (H := pairHecke D T) S hcomm hker
    hcompl


/-- Idempotent specialisation: a Hecke-equivariant idempotent with kernel the
associate pair (equivalently, a Hecke-invariant complement that is a range of an
idempotent) yields the isotypical projection. -/
theorem exists_isotypicalProjection_of_idempotent_kernel
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (S : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hcomm : ∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S)
    (hidem : IsIdempotentElem S)
    (hker : LinearMap.ker S = associatePair D) :
    ∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p :=
  exists_isotypicalProjection_of_semisimple_kernel T S hcomm hker
    (LinearMap.IsIdempotentElem.isCompl hidem).symm


/-- **Converse of the idempotent-kernel criterion.**  From an isotypical projection
`p`, the complementary idempotent `1 - p` is Hecke-equivariant and has kernel exactly
the associate pair.  Hence "an isotypical projection exists" is equivalent to "a
Hecke-equivariant idempotent with kernel the associate pair exists". -/
theorem exists_idempotent_kernel_of_isotypicalProjection
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi)) (hp : IsIsotypicalProjection D T p) :
    ∃ S : Module.End ℂ (BoundaryCoordinates n D.chi),
      IsIdempotentElem S ∧
      (∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S) ∧
      LinearMap.ker S = associatePair D :=
  ⟨LinearMap.id - p,
    exists_idempotent_kernel_of_isProj (A := associatePair D) (H := pairHecke D T) hp⟩

/-- **Existence is equivalent to a Hecke-equivariant idempotent with kernel the
associate pair.** -/
theorem exists_isotypicalProjection_iff_exists_idempotent_kernel
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi), IsIsotypicalProjection D T p) ↔
      ∃ S : Module.End ℂ (BoundaryCoordinates n D.chi),
        IsIdempotentElem S ∧
        (∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S) ∧
        LinearMap.ker S = associatePair D :=
  exists_isProj_iff_exists_idempotent_kernel (A := associatePair D) (H := pairHecke D T)


/-- The complementary idempotent `1 - p` of an isotypical projection `p` is
Hecke-equivariant and has kernel the associate pair. -/
theorem idempotent_kernel_one_sub
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (p : Module.End ℂ (BoundaryCoordinates n D.chi)) (hp : IsIsotypicalProjection D T p) :
    IsIdempotentElem (LinearMap.id - p) ∧
      (∀ t, (LinearMap.id - p).comp (pairHecke D T t) =
        (pairHecke D T t).comp (LinearMap.id - p)) ∧
      LinearMap.ker (LinearMap.id - p) = associatePair D :=
  exists_idempotent_kernel_of_isProj (A := associatePair D) (H := pairHecke D T) hp

/-- The complementary idempotent `1 - S` of a Hecke-equivariant idempotent `S` with
kernel the associate pair is an isotypical projection. -/
theorem isotypical_one_sub
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side))
    (S : Module.End ℂ (BoundaryCoordinates n D.chi))
    (hidem : IsIdempotentElem S)
    (hcomm : ∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S)
    (hker : LinearMap.ker S = associatePair D) :
    IsIsotypicalProjection D T (LinearMap.id - S) :=
  isProj_one_sub (A := associatePair D) (H := pairHecke D T) hidem hcomm hker

/-- **Existence and uniqueness is equivalent to a unique Hecke-equivariant
idempotent with kernel the associate pair.** -/
theorem existsUnique_isotypicalProjection_iff_existsUnique_idempotent_kernel
    (T : (side : Side) → HeckeCorrespondence → Module.End ℂ (StratumH2 n D.chi side)) :
    (∃ p : Module.End ℂ (BoundaryCoordinates n D.chi),
        IsIsotypicalProjection D T p ∧
        ∀ p', IsIsotypicalProjection D T p' → p' = p) ↔
      ∃ S : Module.End ℂ (BoundaryCoordinates n D.chi),
        (IsIdempotentElem S ∧
          (∀ t, S.comp (pairHecke D T t) = (pairHecke D T t).comp S) ∧
          LinearMap.ker S = associatePair D) ∧
        ∀ S' : Module.End ℂ (BoundaryCoordinates n D.chi),
          (IsIdempotentElem S' ∧
            (∀ t, S'.comp (pairHecke D T t) = (pairHecke D T t).comp S') ∧
            LinearMap.ker S' = associatePair D) → S' = S :=
  existsUnique_isProj_iff_existsUnique_idempotent_kernel (A := associatePair D)
    (H := pairHecke D T)

end TernaryPeriodPolynomials.HeckeTranslate.UniversalProjection

end
