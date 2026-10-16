module

public import TernaryPeriodPolynomials.ArithmeticGroup.GL2Free.Generation
public import TernaryPeriodPolynomials.ArithmeticGroup.GL2Free.PingPong

@[expose] public section

open Matrix
noncomputable section
namespace TernaryPoly.IntegralGL2Free
open RelativeStabilizerParameters

def reductionFour : GL2 →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) :=
  Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod 4))

/-- The actual congruence kernel has the parity and diagonal shape used in descent. -/
lemma kernel_reductionFour_good (g : GL2) (hg : g ∈ reductionFour.ker) : Good g := by
  change reductionFour g=1 at hg
  have h (i j : Fin 2) : (g.val i j : ZMod 4)=(1 : Matrix (Fin 2) (Fin 2) (ZMod 4)) i j := by
    exact congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) (ZMod 4) => A.val i j) hg
  have h00 : (g.val 0 0 : ZMod 4)=1 := by simpa using h 0 0
  have h11 : (g.val 1 1 : ZMod 4)=1 := by simpa using h 1 1
  have h01 : (g.val 0 1 : ZMod 4)=0 := by simpa using h 0 1
  have h10 : (g.val 1 0 : ZMod 4)=0 := by simpa using h 1 0
  have ha : g.val 0 0%4=1 := by
    simpa using (ZMod.intCast_eq_intCast_iff' (g.val 0 0) 1 4).mp (by simpa using h00)
  have hd : g.val 1 1%4=1 := by
    simpa using (ZMod.intCast_eq_intCast_iff' (g.val 1 1) 1 4).mp (by simpa using h11)
  have hb : g.val 0 1%4=0 := by
    simpa using (ZMod.intCast_eq_intCast_iff' (g.val 0 1) 0 4).mp (by simpa using h01)
  have hc : g.val 1 0%4=0 := by
    simpa using (ZMod.intCast_eq_intCast_iff' (g.val 1 0) 0 4).mp (by simpa using h10)
  have hdetmod : (g.val.det : ZMod 4)=1 := by
    simp only [Matrix.det_fin_two,Int.cast_sub,Int.cast_mul,h00,h11,h01,h10,
      mul_one,zero_mul,sub_zero]
  have hdet : g.val.det=1 := by
    rcases Int.isUnit_iff.mp ((Matrix.isUnit_iff_isUnit_det g.val).mp g.isUnit) with he | he
    · exact he
    · rw [he] at hdetmod
      have hbad := (ZMod.intCast_eq_intCast_iff' (-1) 1 4).mp (by simpa using hdetmod)
      norm_num at hbad
  exact ⟨hdet,ha,hd,by omega,by omega⟩

lemma kernel_reductionFour_le : reductionFour.ker ≤ generated := by
  intro g hg
  exact good_mem_generated g (kernel_reductionFour_good g hg)

/-- A finite congruence quotient certifies the actual free subgroup's finite index. -/
instance generated_finiteIndex : generated.FiniteIndex :=
  Subgroup.finiteIndex_of_le kernel_reductionFour_le

/-- Actual virtual freeness of the integral GL2, with an explicit free subgroup. -/
theorem exists_finiteIndex_free : ∃ H : Subgroup GL2, H.FiniteIndex ∧ IsFreeGroup H :=
  ⟨generated,inferInstance,inferInstance⟩

end TernaryPoly.IntegralGL2Free
