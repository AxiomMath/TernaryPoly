module

public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.AwaySplit
public import TernaryPeriodPolynomials.ArithmeticGroup.LatticeCounts.LfinGlobal
public import TernaryPeriodPolynomials.ArithmeticCohomology.SphericalDetection.Finite.PlaceIntegralEmbedding

@[expose] public section


open GeneralEisenstein GeneralEisenstein.Adelic MeasureTheory
open TernaryPeriodPolynomials.SphericalDetection.Helpers
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwaySplit
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayStep
open TernaryPeriodPolynomials.Argument.LatticeCounts.AwayMeasure
open TernaryPeriodPolynomials.Argument.LatticeCounts.LocalAdelic

open Classical


/-!
# Global limit, shape lemma (1/2): the explicit splitting of `FiniteAwayThree` at a finite set `S` of places

Formalized by Claude Sonnet 5.5.

For a finite set `S` of places `≠ 3`: `piS S : FiniteAwayThree → ∏_{p∈S} K_p` (local coordinates), `iotaS S` its section (`finiteAwayThreeAtPlace` at each place),
and the explicit additive homeomorphism `eS S : x ↦ (π x, x - ι π x)` onto `(∏_{p∈S} K_p) × awayS S`.  Unlike `AwaySplit.splitFinset_all` (existence only) this one records the first
component, which is what the shape lemma needs.  `eS_symm_measurePreserving`: `eS.symm` carries `localPi S ⊗ awayMeasure S` to the Haar measure of `FiniteAwayThree` (uniqueness of
Haar measure, as in `AwayMeasure.awayStep_symm_measurePreserving`).
-/

noncomputable section
namespace TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit

/-- The product of the completions at the places of `S`. -/
abbrev WS (S : Finset FinitePlace) : Type := ∀ p : S, p.1.adicCompletion ℚ

/-- The local coordinates at the places of `S`. -/
def piS (S : Finset FinitePlace) : FiniteAwayThree →+ WS S :=
  AddMonoidHom.mk' (fun x p => finiteAwayThreeEvaluation p.1 x) (fun x y => by
    funext p; simp)

/-- The embedding of the local coordinates at `S` into `FiniteAwayThree` (zero at the places off `S`). -/
def iotaS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) : WS S →+ FiniteAwayThree :=
  ∑ p : S, (finiteAwayThreeAtPlace p.1 (hS p.1 p.2)).comp (Pi.evalAddMonoidHom (fun p : S => p.1.adicCompletion ℚ) p)

theorem iotaS_apply (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (a : WS S) :
    iotaS S hS a = ∑ p : S, finiteAwayThreeAtPlace p.1 (hS p.1 p.2) (a p) := by
  simp [iotaS]

theorem eval_iotaS_of_mem (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (a : WS S) (w : S) :
    finiteEvaluation w.1 (iotaS S hS a).val = a w := by
  rw [iotaS_apply, AddSubgroup.val_finsetSum, map_sum, Finset.sum_eq_single w]
  · exact finiteAtPlaceScalar_same w.1 _
  · intro p _ hp
    exact finiteAtPlaceScalar_away p.1 _ w.1 (fun h => hp (Subtype.ext h.symm))
  · intro h; exact absurd (Finset.mem_univ w) h

theorem eval_iotaS_of_notMem (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (a : WS S) (w : FinitePlace)
    (hw : w ∉ S) : finiteEvaluation w (iotaS S hS a).val = 0 := by
  rw [iotaS_apply, AddSubgroup.val_finsetSum, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  exact finiteAtPlaceScalar_away p.1 _ w (fun h => hw (h ▸ p.2))

theorem piS_iotaS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (a : WS S) : piS S (iotaS S hS a) = a := by
  funext w
  exact eval_iotaS_of_mem S hS a w

theorem continuous_iotaS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) : Continuous (iotaS S hS) := by
  have : (iotaS S hS : WS S → FiniteAwayThree) = fun a => ∑ p : S, finiteAwayThreeAtPlace p.1 (hS p.1 p.2) (a p) :=
    funext (iotaS_apply S hS)
  rw [this]
  exact continuous_finsetSum _ fun p _ =>
    (finiteAwayThreeAtPlace_continuous p.1 (hS p.1 p.2)).comp (continuous_apply p)

theorem continuous_piS (S : Finset FinitePlace) : Continuous (piS S) :=
  continuous_pi fun p => finiteAwayThreeEvaluation_continuous p.1

/-- A finite adele is integral iff it is integral at every place. -/
theorem mem_range_integralEmbedding_iff (x : FiniteAdeles) :
    x ∈ Set.range integralEmbedding ↔ ∀ w : FinitePlace, finiteEvaluation w x ∈ OS w := by
  constructor
  · rintro ⟨y, rfl⟩ w
    exact (y w).property
  · intro h
    refine ⟨fun w => ⟨finiteEvaluation w x, h w⟩, ?_⟩
    apply IsDedekindDomain.FiniteAdeleRing.ext ℚ
    intro w
    rfl

/-- The remainder `x - ι(π x)` lies in `awayS S`. -/
theorem sub_iota_mem (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (x : FiniteAwayThree) :
    x - iotaS S hS (piS S x) ∈ awayS S := by
  intro p hp
  rw [AddSubgroup.coe_sub, map_sub, eval_iotaS_of_mem S hS (piS S x) ⟨p, hp⟩]
  change finiteEvaluation p x.val - finiteAwayThreeEvaluation p x = 0
  exact sub_self _

/-- **The explicit splitting `FiniteAwayThree ≃ₜ+ (∏_{p∈S} K_p) × awayS S`**, `x ↦ (π x, x - ι π x)`. -/
def eS (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) : FiniteAwayThree ≃ₜ+ WS S × awayS S where
  toFun x := (piS S x, ⟨x - iotaS S hS (piS S x), sub_iota_mem S hS x⟩)
  invFun pr := iotaS S hS pr.1 + pr.2.val
  left_inv x := by
    change iotaS S hS (piS S x) + (x - iotaS S hS (piS S x)) = x
    abel
  right_inv pr := by
    obtain ⟨a, y⟩ := pr
    have hy : piS S y.val = 0 := by
      funext p; exact (mem_awayS.mp y.property) p.1 p.2
    have h1 : piS S (iotaS S hS a + y.val) = a := by
      rw [map_add, piS_iotaS, hy, add_zero]
    refine Prod.ext h1 (Subtype.ext ?_)
    change iotaS S hS a + y.val - iotaS S hS (piS S (iotaS S hS a + y.val)) = y.val
    rw [h1]; abel
  map_add' x y := by
    refine Prod.ext (map_add _ _ _) (Subtype.ext ?_)
    change x + y - iotaS S hS (piS S (x + y)) = (x - iotaS S hS (piS S x)) + (y - iotaS S hS (piS S y))
    rw [map_add, map_add]; abel
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun p => finiteAwayThreeEvaluation_continuous p.1
    · refine Continuous.subtype_mk ?_ _
      exact continuous_id.sub ((continuous_iotaS S hS).comp (continuous_piS S))
  continuous_invFun := by
    exact ((continuous_iotaS S hS).comp continuous_fst).add (continuous_subtype_val.comp continuous_snd)

instance localPi_isAddHaar (S : Finset FinitePlace) : (localPi S).IsAddHaarMeasure :=
  inferInstanceAs (Measure.pi fun p : S => finiteCompletionMeasure p.1).IsAddHaarMeasure

/-- The set of integral points of `awayS S`. -/
abbrev KS (S : Finset FinitePlace) : Set (awayS S) := (fun value : awayS S => value.val.val) ⁻¹' Set.range integralEmbedding

theorem eS_symm_apply (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (pr : WS S × awayS S) :
    ((eS S hS).symm pr).val = (iotaS S hS pr.1).val + pr.2.val.val := rfl

/-- Integrality of `ι a + y` for `y ∈ awayS S`. -/
theorem iota_add_integral_iff (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) (a : WS S)
    (y : awayS S) :
    (iotaS S hS a + y.val).val ∈ Set.range integralEmbedding ↔
      (∀ p : S, a p ∈ OS p.1) ∧ y.val.val ∈ Set.range integralEmbedding := by
  have hy0 : ∀ p : S, finiteEvaluation p.1 y.val.val = 0 := fun p => (mem_awayS.mp y.property) p.1 p.2
  constructor
  · intro h
    rw [mem_range_integralEmbedding_iff] at h
    have ha : ∀ p : S, a p ∈ OS p.1 := by
      intro p
      have := h p.1
      rw [AddSubgroup.coe_add, map_add, hy0 p, add_zero] at this
      rwa [eval_iotaS_of_mem] at this
    refine ⟨ha, ?_⟩
    rw [mem_range_integralEmbedding_iff]
    intro w
    by_cases hw : w ∈ S
    · rw [hy0 ⟨w, hw⟩]; exact (OS w).zero_mem
    · have := h w
      rwa [AddSubgroup.coe_add, map_add, eval_iotaS_of_notMem S hS a w hw, zero_add] at this
  · rintro ⟨ha, hy⟩
    rw [mem_range_integralEmbedding_iff] at hy ⊢
    intro w
    rw [AddSubgroup.coe_add, map_add]
    refine (OS w).add_mem ?_ (hy w)
    by_cases hw : w ∈ S
    · rw [show w = (⟨w, hw⟩ : S).1 from rfl, eval_iotaS_of_mem]
      exact ha ⟨w, hw⟩
    · rw [eval_iotaS_of_notMem S hS a w hw]; exact (OS w).zero_mem

theorem eS_symm_measurePreserving (S : Finset FinitePlace) (hS : ∀ p ∈ S, p ≠ placeThree) :
    MeasurePreserving (eS S hS).symm ((localPi S).prod (awayMeasure S)) finiteAwayThreeMeasure := by
  have hK : MeasurableSet ((finiteAwayThreeUnitCompact : Set FiniteAwayThree)) :=
    (integralLattice_isOpen.preimage continuous_subtype_val).measurableSet
  have preimage : (eS S hS).symm ⁻¹' (finiteAwayThreeUnitCompact : Set FiniteAwayThree) =
      (Set.pi Set.univ fun p : S => ((OS p.1 : Subring _) : Set (p.1.adicCompletion ℚ))) ×ˢ KS S := by
    ext pr
    obtain ⟨a, y⟩ := pr
    change (iotaS S hS a + y.val).val ∈ Set.range integralEmbedding ↔ _
    rw [iota_add_integral_iff]
    simp [Set.mem_prod, Set.mem_pi, KS]
  have normalized : ((localPi S).prod (awayMeasure S))
      ((eS S hS).symm ⁻¹' (finiteAwayThreeUnitCompact : Set FiniteAwayThree)) = 1 := by
    rw [preimage, Measure.prod_prod, awayMeasure_normalized, mul_one, localPi, Measure.pi_pi]
    exact Finset.prod_eq_one fun p _ => finiteCompletionMeasure_normalized p.1
  exact ⟨(eS S hS).symm.continuous.measurable,
    map_eq_addHaarMeasure_of_preimage (eS S hS).symm ((localPi S).prod (awayMeasure S)) finiteAwayThreeUnitCompact hK normalized⟩

end TernaryPeriodPolynomials.Argument.LatticeCounts.GlobalLimitSplit
