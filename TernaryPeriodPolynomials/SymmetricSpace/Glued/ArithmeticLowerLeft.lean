module

public import TernaryPeriodPolynomials.SymmetricSpace.Glued.ArithmeticInterior

@[expose] public section

noncomputable section
namespace TernaryPoly.SymmetricSpaceGluedArithmetic
open Matrix SymmetricSpacePositive SymmetricSpaceFlagCoordinates SymmetricSpaceRationalGluing
open SymmetricSpaceRationalAction SymmetricSpaceCornerSeparation

/-- A positive lower bound for the root monomial cuts out a compact locus wholly in the interior. -/
theorem compact_root_monomial_locus (K L : Set Corner) (hK : IsCompact K) (hL : IsCompact L)
    (ε D : ℝ) (hε : 0<ε) :
    let Z : Set (Corner × Corner) := (K ×ˢ L) ∩
      {z | ε^6≤D^2*z.1.2.1.val^4*z.1.2.2.val^2*z.2.2.1.val^2*z.2.2.2.val^4}
    IsCompact Z ∧ Prod.fst '' Z⊆cornerInterior ∧ Prod.snd '' Z⊆cornerInterior := by
  dsimp only
  refine ⟨(hK.prod hL).inter_right (isClosed_le continuous_const (by fun_prop)),?_,?_⟩
  all_goals
    rintro _ ⟨⟨p,q⟩,⟨_,hz⟩,rfl⟩
    have hpos : 0<D^2*p.2.1.val^4*p.2.2.val^2*q.2.1.val^2*q.2.2.val^4 :=
      (pow_pos hε 6).trans_le hz
    constructor
  · have hn : p.2.1.val≠0 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    exact lt_of_le_of_ne p.2.1.property (Ne.symm hn)
  · have hn : p.2.2.val≠0 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    exact lt_of_le_of_ne p.2.2.property (Ne.symm hn)
  · have hn : q.2.1.val≠0 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    exact lt_of_le_of_ne q.2.1.property (Ne.symm hn)
  · have hn : q.2.2.val≠0 := by
      intro h
      rw [h] at hpos
      norm_num at hpos
    exact lt_of_le_of_ne q.2.2.property (Ne.symm hn)

/-- Nonzero lower-left arithmetic entries force both compact chart endpoints into compact interiors. -/
theorem compact_lowerLeft_chart_transporters (a b : RationalGL) (K L : Set Corner)
    (hK : IsCompact K) (hL : IsCompact L) :
    {g : IntegralGL | (realRational (relative a b g)).val 2 0≠0 ∧
      ∃ p∈K,∃ q∈L,integralAction g (chart a p)=chart b q}.Finite := by
  obtain ⟨d,hd,hden⟩ := relative_hasIntegralDenominator a b
  let ε : ℝ := 1/(d : ℝ)
  have hε : 0<ε := one_div_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hd)
  let D := |(realRational b⁻¹).val.det| * |(realRational a).val.det|
  let Z : Set (Corner × Corner) := (K ×ˢ L) ∩
    {z | ε^6≤D^2*z.1.2.1.val^4*z.1.2.2.val^2*z.2.2.1.val^2*z.2.2.2.val^4}
  obtain ⟨hZ,hZi,hZj⟩ := compact_root_monomial_locus K L hK hL ε D hε
  refine (compact_interior_chart_transporters a b (Prod.fst '' Z) (Prod.snd '' Z)
    (hZ.image continuous_fst) (hZ.image continuous_snd) hZi hZj).subset ?_
  rintro g ⟨hne,p,hp,q,hq,he⟩
  let r := realRational (relative a b g)
  obtain ⟨hdom,ht⟩ := (integral_chart_eq_iff_graph a b g p q).mp he
  change (transition r ⟨p,hdom⟩).val=q at ht
  have hb := transition_lowerLeft_bound r ⟨p,hdom⟩
  change r.val 2 0^6≤r.val.det^2*p.2.1.val^4*p.2.2.val^2*
    (transition r ⟨p,hdom⟩).val.2.1.val^2*(transition r ⟨p,hdom⟩).val.2.2.val^4 at hb
  rw [ht] at hb
  have hdet : r.val.det^2=D^2 := by
    rw [←sq_abs,relative_det_abs]
  rw [hdet] at hb
  have hlo : ε≤|r.val 2 0| := real_denominator_lower_bound d hd _ hne (hden g 2 0)
  have hpow : ε^6≤r.val 2 0^6 := by
    calc
      ε^6≤|r.val 2 0|^6 := by gcongr
      _=(|r.val 2 0|^2)^3 := by ring
      _=(r.val 2 0^2)^3 := by rw [sq_abs]
      _=r.val 2 0^6 := by ring
  have hz : (p,q)∈Z := ⟨⟨hp,hq⟩,hpow.trans hb⟩
  exact ⟨p,⟨(p,q),hz,rfl⟩,q,⟨(p,q),hz,rfl⟩,he⟩

end TernaryPoly.SymmetricSpaceGluedArithmetic
