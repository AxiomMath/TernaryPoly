module

public import TernaryPeriodPolynomials.ModularForm.Symbol.Mobius

@[expose] public section


noncomputable section
namespace TernaryPoly.BinaryCuspSymbol
open BinaryModularSymbol RankTwoAugmentedFrames

/-- The actual rational cusp at infinity is the first coordinate line. -/
def infinity : Line := vectorLine (template 0) (template_ne_zero 0)

/-- The action on infinity is the span of the literal first column. -/
theorem lineAction_infinity_val (g : GL2) :
    (lineAction g infinity).val=Submodule.span ℚ {fun i => g.val i 0} := by
  change Submodule.map (vectorAction g).toLinearMap (Submodule.span ℚ {template 0}) = _
  rw [Submodule.map_span,Set.image_singleton]
  congr 2
  change (Matrix.GeneralLinearGroup.toLin g).toLinearEquiv (Pi.single 0 1) = _
  rw [LinearMap.GeneralLinearGroup.coe_toLinearEquiv,Matrix.GeneralLinearGroup.toLin_apply]
  exact Matrix.mulVec_single_one (g.val) 0

/-- Bézout supplies an integral determinant-one chart for every actual rational cusp. -/
theorem exists_sl_chart (L : Line) : ∃ γ : SL2,lineAction (slRational γ) infinity=L := by
  obtain ⟨v,hp,_,hs⟩ := rationalLine_primitive_generator L
  let g := primitiveCompletion v hp
  let γ : SL2 := ⟨g.val,primitiveCompletion_det v hp⟩
  refine ⟨γ,Subtype.ext ?_⟩
  rw [lineAction_infinity_val]
  have he : (fun i => (slRational γ).val i 0)=rationalVector v := by
    funext i
    change (g.val i 0 : ℚ)=(v i : ℚ)
    exact congrArg (fun z : ℤ => (z : ℚ)) (congrFun (primitiveCompletion_first_column v hp) i)
  rw [he]
  exact hs

/-- A rational matrix fixing infinity has zero lower-left entry. -/
theorem lowerLeft_eq_zero_of_fix_infinity (g : GL2) (h : lineAction g infinity=infinity) :
    g.val 1 0=0 := by
  have he := congrArg Subtype.val h
  rw [lineAction_infinity_val] at he
  change Submodule.span ℚ {fun i => g.val i 0}=Submodule.span ℚ {template 0} at he
  have hm : (fun i => g.val i 0) ∈ Submodule.span ℚ {template 0} := by
    rw [←he]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨q,hq⟩ := Submodule.mem_span_singleton.mp hm
  have hh := congrFun hq 1
  simpa [template] using hh.symm

/-- Two actual charts for the same rational cusp differ by an upper triangular matrix. -/
theorem lowerLeft_eq_zero_of_same_cusp (α β : GL2)
    (h : lineAction α infinity=lineAction β infinity) : (β⁻¹*α).val 1 0=0 := by
  apply lowerLeft_eq_zero_of_fix_infinity
  rw [lineAction_mul,h,←lineAction_mul,inv_mul_cancel,lineAction_one]

end TernaryPoly.BinaryCuspSymbol
