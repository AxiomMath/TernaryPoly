module

public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Translate.TargetFromDecomposition
public import TernaryPeriodPolynomials.ArithmeticGroup.Hecke.Stability.LevelIntersection

@[expose] public section


/-!
# Finite-level invariance of the Hecke translate by coset permutation

The archived reduction `TargetFromDecomposition` needs every `k ∈ finiteLevel` to
fix each finite coset `rf r · finiteLevel`; that input is false in general.  Here the finite-level invariance of the Hecke translate is
derived instead from the permutation property

`(★) ∀ k ∈ finiteLevel, ∀ r ∈ reps, ∃ r' ∈ reps, (rf r')⁻¹ k (rf r) ∈ finiteLevel`,

using that `r ↦ r'` is injective (by `rationalFinite_mem_finiteLevel_iff` and the
disjointness of the representatives), hence a bijection of the finite set of
representatives.  Then `(★)` is derived from the single-coset decomposition
`finiteLevel = rf(Γ) · (finiteLevel ∩ rf r · finiteLevel · (rf r)⁻¹)`.

Original work (AxiomDeep, Claude Opus 5.5).
-/

open GeneralEisenstein
open Homogeneous Adelic Matrix MvPolynomial
open TernaryPeriodPolynomials.HeckeTranslate

noncomputable section

namespace TernaryPeriodPolynomials.HeckeStability

variable {n : ℕ} {D : InducingData n} {side : Side}

/-- The coset-permutation property of a Hecke correspondence. -/
def CosetPermutation (t : HeckeCorrespondence) : Prop :=
  ∀ k ∈ finiteLevel, ∀ r ∈ t.representatives, ∃ r' ∈ t.representatives,
    (rationalFinite r')⁻¹ * k * rationalFinite r ∈ finiteLevel

theorem translateSource_finiteLevel_invariant_of_perm
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hperm : CosetPermutation t) (x : Fin 3 → RealGL3) (g : AdelicGL) (k : finiteLevel) :
    HeckeInvariance.translateSource D t c x (g * atFinite k.val) =
      HeckeInvariance.translateSource D t c x g := by
  classical
  have hone : g * atFinite (1 : GeneralLinearGroup (Fin 3) FiniteAdeles) = g := by
    rw [TranslateRationalLevel.atFinite_one, mul_one]
  rw [TranslateRationalLevel.translateSource_sum_eq t hc x g k.val]
  conv_rhs => rw [← hone]
  rw [TranslateRationalLevel.translateSource_sum_eq t hc x g
    (1 : GeneralLinearGroup (Fin 3) FiniteAdeles)]
  simp only [one_mul]
  rw [← Finset.sum_coe_sort t.representatives]
  conv_rhs => rw [← Finset.sum_coe_sort t.representatives]
  have hchoice : ∀ r : t.representatives, ∃ r' : t.representatives,
      (rationalFinite r'.val)⁻¹ * k.val * rationalFinite r.val ∈ finiteLevel := by
    intro r
    obtain ⟨r', hr', hmem⟩ := hperm k.val k.property r.val r.property
    exact ⟨⟨r', hr'⟩, hmem⟩
  choose σ hσ using hchoice
  have hinj : Function.Injective σ := by
    intro r₁ r₂ heq
    have h₁ := hσ r₁
    have h₂ := hσ r₂
    rw [heq] at h₁
    have hprod := finiteLevel.mul_mem (finiteLevel.inv_mem h₁) h₂
    have hsimp : ((rationalFinite (σ r₂).val)⁻¹ * k.val * rationalFinite r₁.val)⁻¹ *
        ((rationalFinite (σ r₂).val)⁻¹ * k.val * rationalFinite r₂.val) =
        rationalFinite (r₁.val⁻¹ * r₂.val) := by
      rw [map_mul, map_inv]; group
    rw [hsimp] at hprod
    have hlevel := (rationalFinite_mem_finiteLevel_iff _).mp hprod
    exact Subtype.ext (t.disjoint r₁.val r₁.property r₂.val r₂.property hlevel)
  have hbij : Function.Bijective σ := ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hterm : ∀ r : t.representatives,
      c x (g * atFinite (k.val * rationalFinite r.val)) =
        c x (g * atFinite (rationalFinite (σ r).val)) := by
    intro r
    have hm : k.val * rationalFinite r.val = rationalFinite (σ r).val *
        ((rationalFinite (σ r).val)⁻¹ * k.val * rationalFinite r.val) := by group
    rw [hm, ← HeckeInvariance.atFinite_mul, ← mul_assoc]
    exact AveragedHecke.source_level_invariance hc x
      ⟨(rationalFinite (σ r).val)⁻¹ * k.val * rationalFinite r.val, hσ r⟩
      (g * atFinite (rationalFinite (σ r).val))
  rw [Finset.sum_congr rfl (fun r _ => hterm r)]
  exact Fintype.sum_bijective σ hbij _ _ (fun _ => rfl)

/-- Clause (a) of `IsSourceCocycle` for the Hecke translate from `(★)`. -/
theorem translateSource_isInduced_coeff_of_perm
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hperm : CosetPermutation t) (x : Fin 3 → RealGL3) (m : Fin 3 →₀ ℕ) :
    IsInduced D side cohomologicalPoint
      (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m) := by
  apply InducedUpToLevel.isInduced_of_upToLevel
  · have hfun : (fun g => (HeckeInvariance.translateSource D t c x g).val.coeff m)
        = fun g => ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m := by
      funext g
      rw [HeckeInvariance.translateSource]
      rw [show (∑ r ∈ t.representatives, realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val
          = ∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val
          from map_sum (Submodule.subtype (homogeneousSubmodule (Fin 3) ℂ n)) _ _]
      rw [show (∑ r ∈ t.representatives, (realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m
          = ∑ r ∈ t.representatives, ((realCoefficientComponent n D.chi
              (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)
              (c (fun i => (GeneralLinearGroup.map (algebraMap ℚ ℝ) r)⁻¹ * x i)
                (g * rationalGroup r))).val).coeff m
          from map_sum (SourceSmoothness.coeffLM m) _ _]
    rw [hfun]
    apply InducedUpToLevel.isInducedUpToLevel_finset_sum
    intro r _
    exact InducedUpToLevel.isInducedUpToLevel_right_shift r
      (InducedUpToLevel.isInducedUpToLevel_of_isInduced
        (TranslateIsInduced.repCoeff_isInduced hc r x m))
  · intro k g
    exact congrArg (fun p : HomogeneousPoly n => p.val.coeff m)
      (translateSource_finiteLevel_invariant_of_perm t hc hperm x g k)

/-- Source-cocycle closure of the Hecke translate from `(★)`. -/
theorem translateSource_isSourceCocycle_of_perm
    (t : HeckeCorrespondence) {c : SourceCochain n} (hc : IsSourceCocycle D side c)
    (hperm : CosetPermutation t) :
    IsSourceCocycle D side (HeckeInvariance.translateSource D t c) :=
  ⟨fun x m => translateSource_isInduced_coeff_of_perm t hc hperm x m,
   fun m => TranslateHasSmoothCuspLift.translateSource_hasSmoothCuspLift hc t m,
   fun h x g => HeckeInvariance.translateSource_equivariant D t c hc.2.2.1 h x g,
   fun x g => HeckeInvariance.translateSource_closed D t c hc.2.2.2 x g⟩

/-- Hecke stability of each boundary summand under a correspondence with `(★)`. -/
theorem boundarySummand_hecke_stable_of_perm (t : HeckeCorrespondence)
    (hperm : CosetPermutation t)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke)
    (side : Side) :
    ∀ a ∈ boundarySummand D side, hecke side t a ∈ boundarySummand D side :=
  HeckeStability.boundarySummand_hecke_stable t hecke hhecke
    (fun _ _ hc => translateSource_isSourceCocycle_of_perm t hc hperm) side

/-- Hecke stability of the associate pair under a correspondence with `(★)`. -/
theorem associatePair_hecke_stable_of_perm (t : HeckeCorrespondence)
    (hperm : CosetPermutation t)
    (hecke : BoundaryHecke n D.chi) (hhecke : ActualBoundaryHecke n D.chi hecke) :
    ∀ y ∈ associatePair D, pairHecke D hecke t y ∈ associatePair D :=
  HeckeStability.associatePair_hecke_stable t hecke hhecke
    (fun _ _ hc => translateSource_isSourceCocycle_of_perm t hc hperm)

/-- The single-coset decomposition `finiteLevel = rf(Γ) · (finiteLevel ∩ R finiteLevel R⁻¹)`
for every representative `R = rf r`. -/
def CosetDecomposition (t : HeckeCorrespondence) : Prop :=
  ∀ r ∈ t.representatives, ∀ k ∈ finiteLevel, ∃ γ ∈ rationalLevel,
    (rationalFinite γ)⁻¹ * k ∈ finiteLevel ∧
    (rationalFinite r)⁻¹ * ((rationalFinite γ)⁻¹ * k) * rationalFinite r ∈ finiteLevel

theorem cosetPermutation_of_decomposition (t : HeckeCorrespondence)
    (hdec : CosetDecomposition t) : CosetPermutation t := by
  intro k hk r hr
  obtain ⟨γ, hγ, -, hu⟩ := hdec r hr k hk
  obtain ⟨a, b, hab⟩ := t.inDoubleCoset r hr
  obtain ⟨r', hr', hr'mem⟩ := t.complete ⟨γ * a.val, rationalLevel.mul_mem hγ a.property⟩ b
  refine ⟨r', hr', ?_⟩
  have hγr : r'⁻¹ * (γ * r) ∈ rationalLevel := by
    rw [hab]
    simpa only [mul_assoc] using hr'mem
  have hfin := (rationalFinite_mem_finiteLevel_iff _).mpr hγr
  have hprod := finiteLevel.mul_mem hfin hu
  have heq : rationalFinite (r'⁻¹ * (γ * r)) *
      ((rationalFinite r)⁻¹ * ((rationalFinite γ)⁻¹ * k) * rationalFinite r) =
      (rationalFinite r')⁻¹ * k * rationalFinite r := by
    rw [map_mul, map_mul, map_inv]; group
  rw [heq] at hprod
  exact hprod

end TernaryPeriodPolynomials.HeckeStability
