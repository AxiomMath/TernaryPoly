module

public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Good.LineFiniteEndpointValue
public import TernaryPeriodPolynomials.EisensteinSeries.Convergent.Entry.GlobalEntryBridge

@[expose] public section


/-!
# R-e: The finite adelic Euler product of the entry integral (truncation, place by place)

`entryIntegrand` is the finite integrand `v ↦ |det B(v)|^e · φ(m B(v))` of the entry integral, with `B(v)` the `GL₂(𝔸_f)` block of the plane Iwasawa decomposition of `w⁻¹u(v)π` and a left base `m`. The regions `entryRegion S T` (integral outside `T ∪ {3}`, inside a `3`-stable set `S`) are exhausted place by place: `entryIntegral_insert`/`entryIntegral_away` are the Fubini steps at a place `p ≠ 3` (local Euler factor `cuspLocalPadicEulerFactor`), `entryIntegral_product` the induction over finite sets of places, `entryIntegral_eulerProduct` the limit, and `entryBase_univ` the Fubini step at the place `3` for the whole `𝔸_f²`.

Formalized by Claude Sonnet 5.5.
-/


open GeneralEisenstein GeneralEisenstein.Adelic Matrix MeasureTheory Filter
open TernaryPeriodPolynomials.SphericalDetection.Helpers

noncomputable section

namespace TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry

local instance reDecEq : DecidableEq FinitePlace := Classical.decEq _

/-- The `GL₂(𝔸_f)` block of the plane Iwasawa decomposition of `w⁻¹ u(v) π`. -/
def entryBlock (v : FiniteAdeles × FiniteAdeles) : BinaryFiniteGL :=
  (finitePadicPlaneCoordinates v.1 v.2).block

/-- The finite integrand of the entry integral with left base `m`. -/
def entryIntegrand (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (v : FiniteAdeles × FiniteAdeles) : ℂ :=
  normPower (GeneralLinearGroup.det (atFinite (m * entryBlock v))) e *
    cusp.realize vector (atFinite (m * entryBlock v))

/-- A measurable set of adelic pairs whose membership only depends on the `3`-adic components. -/
structure ThreeStable (S : Set (FiniteAdeles × FiniteAdeles)) : Prop where
  measurable : MeasurableSet S
  shift : ∀ v w : FiniteAdeles × FiniteAdeles, finiteThree w.1 = 0 → finiteThree w.2 = 0 →
    (v + w ∈ S ↔ v ∈ S)

/-- Truncation region: integral outside `T ∪ {3}`, inside `S`. -/
def entryRegion (S : Set (FiniteAdeles × FiniteAdeles)) (T : Finset FinitePlace) :
    Set (FiniteAdeles × FiniteAdeles) :=
  {v | v ∈ S ∧ v.1 ∈ finiteIntegralOutside (insert placeThree T) ∧
    v.2 ∈ finiteIntegralOutside (insert placeThree T)}

def entryAwayRegion (S : Set (FiniteAdeles × FiniteAdeles)) (T : Finset FinitePlace) (place : FinitePlace) :
    Set (FiniteAwayPlace place × FiniteAwayPlace place) :=
  {a | (a.1.val, a.2.val) ∈ S ∧
    a.1.val ∈ finiteIntegralOutside (insert placeThree T) ∧ a.2.val ∈ finiteIntegralOutside (insert placeThree T)}

theorem entryRegion_measurable {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (T : Finset FinitePlace) : MeasurableSet (entryRegion S T) := by
  have h1 : MeasurableSet {v : FiniteAdeles × FiniteAdeles | v.1 ∈ finiteIntegralOutside (insert placeThree T)} :=
    (finiteIntegralOutside_measurable _).preimage measurable_fst
  have h2 : MeasurableSet {v : FiniteAdeles × FiniteAdeles | v.2 ∈ finiteIntegralOutside (insert placeThree T)} :=
    (finiteIntegralOutside_measurable _).preimage measurable_snd
  exact hS.measurable.inter (h1.inter h2)

theorem entryRegion_mono (S : Set (FiniteAdeles × FiniteAdeles)) : Monotone (entryRegion S) := by
  intro first second included v member
  exact ⟨member.1, finiteIntegralOutside_mono (Finset.insert_subset_insert _ included) member.2.1,
    finiteIntegralOutside_mono (Finset.insert_subset_insert _ included) member.2.2⟩

theorem entryRegion_union (S : Set (FiniteAdeles × FiniteAdeles)) :
    (⋃ T, entryRegion S T) = S := by
  ext v
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨T, member⟩
    exact member.1
  · intro member
    have first : v.1 ∈ ⋃ T, finiteIntegralOutside T := by rw [finiteIntegralOutside_union]; trivial
    have second : v.2 ∈ ⋃ T, finiteIntegralOutside T := by rw [finiteIntegralOutside_union]; trivial
    obtain ⟨T₁, h₁⟩ := Set.mem_iUnion.mp first
    obtain ⟨T₂, h₂⟩ := Set.mem_iUnion.mp second
    refine ⟨T₁ ∪ T₂, member, ?_, ?_⟩
    · exact finiteIntegralOutside_mono ((Finset.subset_union_left (s₂ := T₂)).trans (Finset.subset_insert _ _)) h₁
    · exact finiteIntegralOutside_mono ((Finset.subset_union_right (s₁ := T₁)).trans (Finset.subset_insert _ _)) h₂

theorem entryRegion_insert_three (S : Set (FiniteAdeles × FiniteAdeles)) (T : Finset FinitePlace) :
    entryRegion S (insert placeThree T) = entryRegion S T := by
  rw [entryRegion, entryRegion, Finset.insert_idem]


theorem entryIntegrand_join (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      entryIntegrand cusp vector m e (finitePadicRadicalJoin place (localPair, awayPair)) =
        cuspLocalPadicIntegrand cusp vector (m * entryBlock (awayPair.1.val, awayPair.2.val)) place e localPair := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  unfold entryIntegrand entryBlock
  rw [finitePadicRadicalJoin_apply]
  dsimp only
  rw [finitePadicPlaneCoordinates_split_block, ← mul_assoc]
  rfl


theorem entryJoin_apply (place : FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicRadicalJoin place (localPair, awayPair) =
        (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + awayPair.1.val,
         finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + awayPair.2.val) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  rw [finitePadicRadicalJoin_apply, finitePadicSplit_symm, finitePadicSplit_symm]

theorem entryJoin_mem {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S) (place : FinitePlace)
    (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicRadicalJoin place (localPair, awayPair) ∈ S ↔ (awayPair.1.val, awayPair.2.val) ∈ S := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  rw [entryJoin_apply]
  have equal : (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + awayPair.1.val,
      finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + awayPair.2.val) =
      (awayPair.1.val, awayPair.2.val) +
      (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1),
       finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2)) :=
    Prod.ext (add_comm _ _) (add_comm _ _)
  rw [equal]
  exact hS.shift (awayPair.1.val, awayPair.2.val)
    (finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1),
     finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2))
    (finiteAtPlaceScalar_three place distinct _) (finiteAtPlaceScalar_three place distinct _)

theorem entryRegion_join_mem_insert {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicRadicalJoin place (localPair, awayPair) ∈ entryRegion S (insert place T) ↔
        awayPair ∈ entryAwayRegion S T place := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  have order : insert placeThree (insert place T) = insert place (insert placeThree T) :=
    Finset.insert_comm _ _ _
  have first := finiteIntegralOutside_add_single (insert placeThree (insert place T)) place
    ((finiteCompletionPadicEquiv place).symm localPair.1) awayPair.1.val awayPair.1.property
  have second := finiteIntegralOutside_add_single (insert placeThree (insert place T)) place
    ((finiteCompletionPadicEquiv place).symm localPair.2) awayPair.2.val awayPair.2.property
  have first' := finiteIntegralOutside_insert_zero (insert placeThree T) place awayPair.1.val awayPair.1.property
  have second' := finiteIntegralOutside_insert_zero (insert placeThree T) place awayPair.2.val awayPair.2.property
  rw [← order] at first' second'
  refine and_congr (entryJoin_mem hS place distinct localPair awayPair) (and_congr ?_ ?_)
  · change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + awayPair.1.val ∈ _ ↔ _
    rw [first, first']
    simp
  · change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + awayPair.2.val ∈ _ ↔ _
    rw [second, second']
    simp

theorem entryRegion_join_mem {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ T) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    ∀ (localPair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] × ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val])
      (awayPair : FiniteAwayPlace place × FiniteAwayPlace place),
      finitePadicRadicalJoin place (localPair, awayPair) ∈ entryRegion S T ↔
        (‖localPair.1‖ ≤ 1 ∧ ‖localPair.2‖ ≤ 1) ∧ awayPair ∈ entryAwayRegion S T place := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  intro localPair awayPair
  have notMem : place ∉ insert placeThree T := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨distinct, outside⟩
  have first := finiteIntegralOutside_add_single (insert placeThree T) place
    ((finiteCompletionPadicEquiv place).symm localPair.1) awayPair.1.val awayPair.1.property
  have second := finiteIntegralOutside_add_single (insert placeThree T) place
    ((finiteCompletionPadicEquiv place).symm localPair.2) awayPair.2.val awayPair.2.property
  have norm₁ : ‖localPair.1‖ ≤ 1 ↔ (finiteCompletionPadicEquiv place).symm localPair.1 ∈
      place.adicCompletionIntegers ℚ := by
    rw [← finiteCompletionPadic_integral_iff, RingEquiv.apply_symm_apply]
  have norm₂ : ‖localPair.2‖ ≤ 1 ↔ (finiteCompletionPadicEquiv place).symm localPair.2 ∈
      place.adicCompletionIntegers ℚ := by
    rw [← finiteCompletionPadic_integral_iff, RingEquiv.apply_symm_apply]
  have s := entryJoin_mem hS place distinct localPair awayPair
  change finitePadicRadicalJoin place (localPair, awayPair) ∈ S ∧ _ ∧ _ ↔ _
  constructor
  · rintro ⟨h₀, h₁, h₂⟩
    rw [entryJoin_apply] at h₁ h₂
    change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + awayPair.1.val ∈ _ at h₁
    change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + awayPair.2.val ∈ _ at h₂
    rw [first] at h₁
    rw [second] at h₂
    exact ⟨⟨norm₁.mpr (h₁.1 notMem), norm₂.mpr (h₂.1 notMem)⟩, s.mp h₀, h₁.2, h₂.2⟩
  · rintro ⟨⟨n₁, n₂⟩, h₀, h₁, h₂⟩
    refine ⟨s.mpr h₀, ?_, ?_⟩
    · rw [entryJoin_apply]
      change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.1) + awayPair.1.val ∈ _
      rw [first]
      exact ⟨fun _ => norm₁.mp n₁, h₁⟩
    · rw [entryJoin_apply]
      change finiteAtPlaceScalar place ((finiteCompletionPadicEquiv place).symm localPair.2) + awayPair.2.val ∈ _
      rw [second]
      exact ⟨fun _ => norm₂.mp n₂, h₂⟩


theorem entryRegion_preimage_insert {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finitePadicRadicalJoin place) ⁻¹' entryRegion S (insert place T) =
      Set.univ ×ˢ entryAwayRegion S T place := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  ext ⟨localPair, awayPair⟩
  exact (entryRegion_join_mem_insert hS T place distinct localPair awayPair).trans
    (by simp)

theorem entryRegion_preimage {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ T) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
    (finitePadicRadicalJoin place) ⁻¹' entryRegion S T =
      {pair : ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] ×
        ℚ_[(Rat.HeightOneSpectrum.primesEquiv place).val] | ‖pair.1‖ ≤ 1 ∧ ‖pair.2‖ ≤ 1} ×ˢ
        entryAwayRegion S T place := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  ext ⟨localPair, awayPair⟩
  exact entryRegion_join_mem hS T place distinct outside localPair awayPair

theorem entryIntegral_away {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) (outside : place ∉ T)
    (integrable : Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure)) :
    (∫ v in entryRegion S T, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      ∫ a in entryAwayRegion S T place, entryIntegrand cusp vector m e (a.1.val, a.2.val)
        ∂((finiteAwayPlaceMeasure place).prod (finiteAwayPlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have lifted := (finitePadicRadicalJoin_measurePreserving place).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [← (finitePadicRadicalJoin_measurePreserving place).setIntegral_preimage_emb
      (finitePadicRadicalJoin place).measurableEmbedding, entryRegion_preimage hS T place distinct outside]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [entryIntegrand_join, cuspLocalPadicIntegral_square]
  rfl

theorem entryIntegral_insert {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 2 < e.re)
    (T : Finset FinitePlace) (place : FinitePlace) (distinct : place ≠ placeThree) (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalue • vector)
    (integrable : Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure)) :
    (∫ v in entryRegion S (insert place T), entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      cuspLocalPadicEulerFactor cusp place eigenvalue e *
        ∫ a in entryAwayRegion S T place, entryIntegrand cusp vector m e (a.1.val, a.2.val)
          ∂((finiteAwayPlaceMeasure place).prod (finiteAwayPlaceMeasure place)) := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  have lifted := (finitePadicRadicalJoin_measurePreserving place).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [← (finitePadicRadicalJoin_measurePreserving place).setIntegral_preimage_emb
      (finitePadicRadicalJoin place).measurableEmbedding, entryRegion_preimage_insert hS T place distinct]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [setIntegral_univ, entryIntegrand_join,
    cuspLocalPadicIntegral_eulerQuotient cusp vector nonzero spherical _ place e convergent eigenvalue eigen]
  simp_rw [cuspLocalPadicEulerFactor, mul_assoc]
  rw [← integral_const_mul]
  rfl


theorem entryIntegral_product {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 2 < e.re)
    (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree →
      cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalues place • vector)
    (integrable : Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure))
    (T : Finset FinitePlace) :
    (∫ v in entryRegion S T, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      (∏ place ∈ T, cuspLocalPadicEulerFactorAwayThree cusp eigenvalues e place) *
        ∫ v in entryRegion S ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure) := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty, one_mul]
  | @insert place T outside induction =>
    by_cases same : place = placeThree
    · subst place
      rw [entryRegion_insert_three, induction, Finset.prod_insert outside,
        cuspLocalPadicEulerFactorAwayThree, ite_eq_left rfl, one_mul]
    · rw [entryIntegral_insert hS cusp vector nonzero spherical m e convergent T place same (eigenvalues place)
        (eigen place same) integrable, ← entryIntegral_away hS cusp vector m e T place same outside integrable,
        induction, Finset.prod_insert outside, cuspLocalPadicEulerFactorAwayThree, ite_eq_right same, mul_assoc]

theorem entryIntegral_tendsto {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (value : FiniteAdeles × FiniteAdeles → ℂ) (integrable : Integrable value (finiteMeasure.prod finiteMeasure)) :
    Tendsto (fun T : Finset FinitePlace => ∫ v in entryRegion S T, value v ∂(finiteMeasure.prod finiteMeasure))
      atTop (nhds (∫ v in S, value v ∂(finiteMeasure.prod finiteMeasure))) := by
  have limit := tendsto_setIntegral_of_monotone (entryRegion_measurable hS) (entryRegion_mono S)
    (show IntegrableOn value (⋃ T, entryRegion S T) (finiteMeasure.prod finiteMeasure) from
      integrable.integrableOn)
  rwa [entryRegion_union] at limit

theorem entryIntegral_eulerProduct {S : Set (FiniteAdeles × FiniteAdeles)} (hS : ThreeStable S)
    (cusp : CuspidalRepresentation) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 2 < e.re)
    (eigenvalues : FinitePlace → ℂ)
    (eigen : ∀ place, place ≠ placeThree →
      cuspLocalPadicSphereOperator cusp place 1 vector = eigenvalues place • vector)
    (integrable : Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure))
    (value : ℂ) (product : HasProd (fun place : {place : FinitePlace // place ≠ placeThree} =>
      cuspLocalPadicEulerFactor cusp place.val (eigenvalues place.val) e) value) :
    (∫ v in S, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      value * ∫ v in entryRegion S ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure) := by
  have limit := entryIntegral_tendsto hS _ integrable
  have extended := cuspLocalPadicEulerFactorAwayThree_hasProd cusp eigenvalues e value product
  have product_limit : Tendsto (fun T : Finset FinitePlace =>
      ∏ place ∈ T, cuspLocalPadicEulerFactorAwayThree cusp eigenvalues e place) atTop (nhds value) := extended
  have weighted : Tendsto (fun T : Finset FinitePlace => ∫ v in entryRegion S T,
      entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) atTop
      (nhds (value * ∫ v in entryRegion S ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure))) := by
    convert product_limit.mul_const
      (∫ v in entryRegion S ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) using 1
    funext T
    exact entryIntegral_product hS cusp vector nonzero spherical m e convergent eigenvalues eigen integrable T
  exact tendsto_nhds_unique limit weighted


/-- On the integral points the `GL₂` block is the identity. -/
theorem entryBlock_eq_one (v : FiniteAdeles × FiniteAdeles) (h₁ : v.1 ∈ finiteIntegralOutside ∅)
    (h₂ : v.2 ∈ finiteIntegralOutside ∅) : entryBlock v = 1 := by
  apply finitePadicGeneralLinearGroup_ext
  intro place
  let : Fact (Rat.HeightOneSpectrum.primesEquiv place).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv place).property⟩
  rw [map_one]
  unfold entryBlock
  have n₁ : ‖finitePadicEvaluation place v.1‖ ≤ 1 :=
    (finiteCompletionPadic_integral_iff place _).mpr (h₁ place (Finset.notMem_empty place))
  have n₂ : ‖finitePadicEvaluation place v.2‖ ≤ 1 :=
    (finiteCompletionPadic_integral_iff place _).mpr (h₂ place (Finset.notMem_empty place))
  rw [finitePadicPlaneCoordinates_block, padicPlanePivotCoordinates_integral _ _ n₁ n₂]

theorem entryIntegrand_integral (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ)
    (v : FiniteAdeles × FiniteAdeles) (h₁ : v.1 ∈ finiteIntegralOutside ∅) (h₂ : v.2 ∈ finiteIntegralOutside ∅) :
    entryIntegrand cusp vector m e v =
      normPower (GeneralLinearGroup.det (atFinite m)) e * cusp.realize vector (atFinite m) := by
  unfold entryIntegrand
  rw [entryBlock_eq_one v h₁ h₂, mul_one]

/-- The base value of the `3`-adic and all-places Euler product. -/
def entryBaseValue (cusp : CuspidalRepresentation) (vector : cusp.smooth) (m : BinaryFiniteGL) (e : ℂ) : ℂ :=
  normPower (GeneralLinearGroup.det (atFinite m)) e * cusp.realize vector (atFinite m)

theorem entryAwayRegion_univ_three :
    entryAwayRegion Set.univ ∅ placeThree =
      (Subtype.val ⁻¹' Set.range integralEmbedding) ×ˢ (Subtype.val ⁻¹' Set.range integralEmbedding) := by
  ext a
  have first := finiteIntegralOutside_insert_zero (∅ : Finset FinitePlace) placeThree a.1.val a.1.property
  have second := finiteIntegralOutside_insert_zero (∅ : Finset FinitePlace) placeThree a.2.val a.2.property
  simp only [entryAwayRegion, Set.mem_ofPred_eq, Set.mem_univ, true_and, Set.mem_prod, Set.mem_preimage]
  rw [first, second, finiteIntegralOutside_empty]

theorem entryRegion_preimage_three (T : Finset FinitePlace) :
    letI : Fact (Rat.HeightOneSpectrum.primesEquiv placeThree).val.Prime :=
      ⟨(Rat.HeightOneSpectrum.primesEquiv placeThree).property⟩
    (finitePadicRadicalJoin placeThree) ⁻¹' entryRegion Set.univ T =
      Set.univ ×ˢ entryAwayRegion Set.univ T placeThree := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv placeThree).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv placeThree).property⟩
  ext ⟨localPair, awayPair⟩
  have first := finiteIntegralOutside_add_single (insert placeThree T) placeThree
    ((finiteCompletionPadicEquiv placeThree).symm localPair.1) awayPair.1.val awayPair.1.property
  have second := finiteIntegralOutside_add_single (insert placeThree T) placeThree
    ((finiteCompletionPadicEquiv placeThree).symm localPair.2) awayPair.2.val awayPair.2.property
  constructor
  · rintro ⟨_, h₁, h₂⟩
    rw [entryJoin_apply] at h₁ h₂
    change finiteAtPlaceScalar placeThree ((finiteCompletionPadicEquiv placeThree).symm localPair.1) +
      awayPair.1.val ∈ finiteIntegralOutside (insert placeThree T) at h₁
    change finiteAtPlaceScalar placeThree ((finiteCompletionPadicEquiv placeThree).symm localPair.2) +
      awayPair.2.val ∈ finiteIntegralOutside (insert placeThree T) at h₂
    rw [first] at h₁
    rw [second] at h₂
    exact ⟨trivial, trivial, h₁.2, h₂.2⟩
  · rintro ⟨_, _, h₁, h₂⟩
    refine ⟨trivial, ?_, ?_⟩
    · rw [entryJoin_apply]
      change finiteAtPlaceScalar placeThree ((finiteCompletionPadicEquiv placeThree).symm localPair.1) +
        awayPair.1.val ∈ finiteIntegralOutside (insert placeThree T)
      rw [first]
      exact ⟨fun h => absurd (Finset.mem_insert_self _ _) h, h₁⟩
    · rw [entryJoin_apply]
      change finiteAtPlaceScalar placeThree ((finiteCompletionPadicEquiv placeThree).symm localPair.2) +
        awayPair.2.val ∈ finiteIntegralOutside (insert placeThree T)
      rw [second]
      exact ⟨fun h => absurd (Finset.mem_insert_self _ _) h, h₂⟩


theorem entryBase_univ (cusp : CuspidalRepresentation) (vector : cusp.smooth) (nonzero : vector ≠ 0)
    (spherical : vector.val ∈ cuspSphericalValues cusp) (m : BinaryFiniteGL) (e : ℂ) (convergent : 2 < e.re)
    (eigenvalue : ℂ)
    (eigen : cuspLocalPadicSphereOperator cusp placeThree 1 vector = eigenvalue • vector)
    (integrable : Integrable (entryIntegrand cusp vector m e) (finiteMeasure.prod finiteMeasure)) :
    (∫ v in entryRegion Set.univ ∅, entryIntegrand cusp vector m e v ∂(finiteMeasure.prod finiteMeasure)) =
      cuspLocalPadicEulerFactor cusp placeThree eigenvalue e * entryBaseValue cusp vector m e := by
  let : Fact (Rat.HeightOneSpectrum.primesEquiv placeThree).val.Prime :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv placeThree).property⟩
  have lifted := (finitePadicRadicalJoin_measurePreserving placeThree).integrable_comp_of_integrable integrable
  simp only [Function.comp_def] at lifted
  rw [← (finitePadicRadicalJoin_measurePreserving placeThree).setIntegral_preimage_emb
      (finitePadicRadicalJoin placeThree).measurableEmbedding, entryRegion_preimage_three]
  rw [setIntegral_prod_symm_of_integrable _ _ _ _ _ lifted.integrableOn]
  simp_rw [setIntegral_univ, entryIntegrand_join,
    cuspLocalPadicIntegral_eulerQuotient cusp vector nonzero spherical _ placeThree e convergent eigenvalue eigen]
  have constant : Set.EqOn (fun a : FiniteAwayPlace placeThree × FiniteAwayPlace placeThree =>
      (1 - eigenvalue / ((Rat.HeightOneSpectrum.primesEquiv placeThree).val : ℂ) *
          padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv placeThree).val e +
        cuspLocalPadicCentralChar cusp placeThree / ((Rat.HeightOneSpectrum.primesEquiv placeThree).val : ℂ) *
          padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv placeThree).val e ^ 2) /
        (1 - eigenvalue * padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv placeThree).val e +
          ((Rat.HeightOneSpectrum.primesEquiv placeThree).val : ℂ) * cuspLocalPadicCentralChar cusp placeThree *
            padicPrimitiveSeriesScale (Rat.HeightOneSpectrum.primesEquiv placeThree).val e ^ 2) *
        normPower (GeneralLinearGroup.det (atFinite (m * entryBlock (a.1.val, a.2.val)))) e *
        cusp.realize vector (atFinite (m * entryBlock (a.1.val, a.2.val))))
      (fun _ => cuspLocalPadicEulerFactor cusp placeThree eigenvalue e * entryBaseValue cusp vector m e)
      (entryAwayRegion Set.univ ∅ placeThree) := by
    intro a member
    rw [entryAwayRegion_univ_three] at member
    obtain ⟨h₁, h₂⟩ := member
    have h₁' : (a.1.val, a.2.val).1 ∈ finiteIntegralOutside ∅ := by
      rw [finiteIntegralOutside_empty]; exact h₁
    have h₂' : (a.1.val, a.2.val).2 ∈ finiteIntegralOutside ∅ := by
      rw [finiteIntegralOutside_empty]; exact h₂
    beta_reduce
    rw [entryBlock_eq_one _ h₁' h₂', mul_one]
    unfold cuspLocalPadicEulerFactor entryBaseValue
    simp only [mul_assoc]
  rw [setIntegral_congr_fun ?_ constant, setIntegral_const]
  · rw [entryAwayRegion_univ_three, Measure.real, Measure.prod_prod, finiteAwayPlaceMeasure_normalized, mul_one,
      ENNReal.toReal_one, one_smul]
  · rw [entryAwayRegion_univ_three]
    exact (integralLattice_isOpen.preimage continuous_subtype_val).measurableSet.prod
      (integralLattice_isOpen.preimage continuous_subtype_val).measurableSet

end TernaryPeriodPolynomials.Argument.ConvergentEisenstein.Entry
