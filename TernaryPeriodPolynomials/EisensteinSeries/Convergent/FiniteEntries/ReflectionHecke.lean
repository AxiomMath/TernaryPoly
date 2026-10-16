module

public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.ReflectionSign
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.FiniteEntries.HeckeCluster

@[expose] public section



/-!
# Hecke-equivariance of extendedness over `⟨K†, -I₃⟩`

* `isReflExtended_hecke`: for any realization of the Hecke correspondences on the flag cohomology
  (`RealizesHecke`), the Hecke image of a class that extends over `⟨K†, -I₃⟩` extends again.  The Hecke cochain
  `x ↦ ∑_r ρ(r) c(r⁻¹ x)` of a `-I₃`-equivariant cochain `c` is `-I₃`-equivariant because `-I₃` is central
  (`ρ(r) ρ(z) = ρ(z) ρ(r)`), and a `K†`-cocycle which is `z`-equivariant is a cocycle of the extended level
  (`CentralExtension.extendCocycle`).
* `reflExtendedPair`, `cluster_sum_extended`: the submodule of boundary pairs with extended coordinates is stable under
  every `pairHecke`, so by the Lagrange-interpolation lemma `cluster_mem` the partial sum of an extended pair-level
  family over any Hecke-character class is extended.
* `chi_eq_trivial_of_extended_sum_bad_plane`: for a finite family of data with the same inducing character `χ` (hence the
  same stratum), an extended sum of classes `f i ∈ boundarySummand (D i)` with nonzero bad-plane coordinate forces
  `χ = trivialCharacter`.  This is the datum-level theorem for the actual decomposition `ξ = ∑ f D`; it needs no
  separation of the summands.

Note: Hecke operators cannot separate two data with the same away-three pair character, so the Hecke-equivariance gives
extendedness of each character-class sum, not of each individual `f D`; the sum version above is what the character
argument needs.

Formalized by Claude Sonnet 5.5.
-/

open GeneralEisenstein GeneralEisenstein.Adelic GeneralEisenstein.Homogeneous
open TernaryPeriodPolynomials.Spectral.CuspReduction

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries

/-- `c • x = 0` over `ℂ` (proved for an arbitrary module so that the instance problem is not
re-solved on the concrete cohomology space). -/
private theorem complex_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] {c : ℂ} {x : V}
    (h : c • x = 0) : c = 0 ∨ x = 0 :=
  smul_eq_zero.mp h


/-- The Hecke cochain of a `-I₃`-equivariant cochain is `-I₃`-equivariant. -/
theorem heckeCochain_reflZ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ RationalGL3 V)
    (t : HeckeCorrespondence) (c : cochains rationalLevel ρ 2)
    (hc : ∀ x, c.val (fun i => reflZ * x i) = ρ reflZ (c.val x)) (x : Fin 3 → RationalGL3) :
    heckeCochain ρ t c (fun i => reflZ * x i) = ρ reflZ (heckeCochain ρ t c x) := by
  unfold heckeCochain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  have e : (fun i => r⁻¹ * (reflZ * x i)) = fun i => reflZ * (r⁻¹ * x i) := by
    funext i
    rw [← mul_assoc, ← mul_assoc]
    congr 1
    have := reflZ_comm r⁻¹
    exact this.symm
  rw [e, hc, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, reflZ_comm r]

/-- **The Hecke image of an extended class is extended.** -/
theorem isReflExtended_hecke {n : ℕ} {χ : RankOneCharacter} {s : Side}
    (T : HeckeCorrespondence → Module.End ℂ (StratumH2 n χ s))
    (hT : RealizesHecke (flagRepresentation (rationalCoefficientComponent n χ) s) T)
    (t : HeckeCorrespondence) {a : StratumH2 n χ s} (ha : IsReflExtended a) : IsReflExtended (T t a) := by
  obtain ⟨c', rfl⟩ := ha
  have hobtain1 := hT t (resCocycle _ rationalLevel_le_reflLevel c')
  obtain ⟨z, hz, hTz⟩ := hobtain1
  rw [hTz]
  have hc : ∀ x, (resCocycle _ rationalLevel_le_reflLevel c').val.val (fun i => reflZ * x i) =
      flagRepresentation (rationalCoefficientComponent n χ) s reflZ
        ((resCocycle _ rationalLevel_le_reflLevel c').val.val x) :=
    fun x => c'.val.property ⟨reflZ, reflZ_mem_reflLevel⟩ x
  have hzeq : ∀ x, z.val.val (fun i => reflZ * x i) =
      flagRepresentation (rationalCoefficientComponent n χ) s reflZ (z.val.val x) := by
    intro x
    rw [hz, hz]
    exact heckeCochain_reflZ _ t _ hc x
  exact ⟨extendCocycle rationalLevel reflZ reflZ_comm reflZ_sq _ z hzeq, rfl⟩

/-- The classes of the stratum that extend over `⟨K†, -I₃⟩`. -/
def reflExtended (n : ℕ) (χ : RankOneCharacter) (s : Side) : Submodule ℂ (StratumH2 n χ s) :=
  LinearMap.range ((classOf rationalLevel (flagRepresentation (rationalCoefficientComponent n χ) s)).comp
    (resCocycle _ rationalLevel_le_reflLevel))

theorem mem_reflExtended {n : ℕ} {χ : RankOneCharacter} {s : Side} {a : StratumH2 n χ s} :
    a ∈ reflExtended n χ s ↔ IsReflExtended a := Iff.rfl

/-- Boundary pairs with both coordinates extended. -/
def reflExtendedPair (n : ℕ) (χ : RankOneCharacter) : Submodule ℂ (BoundaryCoordinates n χ) :=
  (reflExtended n χ .plane).prod (reflExtended n χ .line)

theorem pairHecke_mem_reflExtendedPair {n : ℕ} (D : InducingData n) (hecke : BoundaryHecke n D.chi)
    (hhecke : ActualBoundaryHecke n D.chi hecke) (t : HeckeCorrespondence) {b : BoundaryCoordinates n D.chi}
    (hb : b ∈ reflExtendedPair n D.chi) : pairHecke D hecke t b ∈ reflExtendedPair n D.chi :=
  ⟨isReflExtended_hecke (hecke .plane) (hhecke .plane) t hb.1,
    isReflExtended_hecke (hecke .line) (hhecke .line) t hb.2⟩

open Classical in
/-- **Character-class sums of an extended family are extended.** -/
theorem cluster_sum_extended {n : ℕ} {ι : Type*} (D₀ : InducingData n) (hecke : BoundaryHecke n D₀.chi)
    (hhecke : ActualBoundaryHecke n D₀.chi hecke) (S : Finset ι) (v : ι → BoundaryCoordinates n D₀.chi)
    (ch : ι → {t : HeckeCorrespondence // AwayThree t} → ℂ)
    (heig : ∀ i ∈ S, ∀ j : {t : HeckeCorrespondence // AwayThree t},
      pairHecke D₀ hecke j.1 (v i) = ch i j • v i)
    (hsum : ∑ i ∈ S, v i ∈ reflExtendedPair n D₀.chi) (i₀ : ι) :
    ∑ i ∈ S.filter (fun i => ch i = ch i₀), v i ∈ reflExtendedPair n D₀.chi :=
  cluster_mem (reflExtendedPair n D₀.chi) (fun j => pairHecke D₀ hecke j.1)
    (fun j _ hx => pairHecke_mem_reflExtendedPair D₀ hecke hhecke j.1 hx) S v ch heig hsum i₀

/-- **The datum-level character theorem for a decomposition.**  A finite family of data with the common inducing
character `χ` (so the summands lie in the common stratum `StratumH2 n χ plane`), whose extended sum has a nonzero bad-plane
coordinate, has `χ = trivialCharacter`. -/
theorem chi_eq_trivial_of_extended_sum_bad_plane {n : ℕ} {ι : Type*} (χ : RankOneCharacter) (S : Finset ι)
    (cusp : ι → CuspidalRepresentation) (coh : ∀ i, Cohomological (cusp i) n)
    (f : ι → StratumH2 n χ .plane)
    (hf : ∀ i ∈ S, f i ∈ boundarySummand (⟨cusp i, χ, coh i⟩ : InducingData n) .plane)
    (hext : IsReflExtended (∑ i ∈ S, f i)) (hbad : cuspRes n χ .plane false (∑ i ∈ S, f i) ≠ 0) :
    χ = trivialCharacter := by
  obtain ⟨i, hi, hne⟩ : ∃ i ∈ S, cuspRes n χ .plane false (f i) ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hbad
    rw [map_sum]
    exact Finset.sum_eq_zero hall
  let D : InducingData n := ⟨cusp i, χ, coh i⟩
  have hsph : SphericalCusp D.cusp := by
    by_contra hns
    exact hne (TernaryPeriodPolynomials.Separation.cuspRes_plane_false_eq_zero_of_not_spherical
      D hns (hf i hi))
  have hodd : Odd n :=
    TernaryPeriodPolynomials.LevelOneCohomologicalParity.Helpers.cohomological_spherical_odd n D.cusp
      D.cohomological hsph
  obtain ⟨c', hc'⟩ := hext
  have h := reflScalar_sub_one_smul_extended n χ .plane c'
  rw [hc'] at h
  have hane : (∑ i ∈ S, f i) ≠ 0 := fun h0 => hbad (by rw [h0, map_zero])
  have hs : reflScalar n χ = 1 := sub_eq_zero.mp ((complex_smul_eq_zero h).resolve_right hane)
  unfold reflScalar at hs
  rw [(hodd.add_one).neg_one_pow, mul_one] at hs
  have hfne : f i ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
  have hpair : associatePair D ≠ ⊥ := by
    intro hbot
    have hmem : ((f i, 0) : BoundaryCoordinates n D.chi) ∈ associatePair D := ⟨hf i hi, Submodule.zero_mem _⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact hfne (congrArg Prod.fst hmem)
  exact chi_eq_trivial_of_pair_even D hpair hs

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.FiniteEntries
