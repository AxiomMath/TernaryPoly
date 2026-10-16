module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapRelative

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory HomologicalComplex
open SingularLocalCap SingularLocalCap.Descent

/-- The cap Leibniz identity forces the precise boundary sign on any relative scalar cycle. -/
theorem cap_boundary_sign
    (C : CochainComplex (ModuleCat.{0} ℚ) ℕ) (K L : ChainComplex (ModuleCat.{0} ℚ) ℕ)
    (β : ∀ a b, C.X a →ₗ[ℚ] K.X (a+b) →ₗ[ℚ] L.X b) (hβ : Leibniz C K L β)
    (a b : ℕ) (x : C.X a) (c : K.X (a+b+1)) (hc : K.d (a+b+1) (a+b) c = 0) :
    L.d (b+1) b (β a (b+1) x c) =
      (-1 : ℤ)^(a+1) • β (a+1) b (C.d a (a+1) x) ((castLeft K a b).hom c) := by
  have hs : (-1 : ℤ)^a * (-1 : ℤ)^a = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have h := hβ a b x c
  rw [hc,map_zero] at h
  have hh := congrArg (fun z => (-1 : ℤ)^a • z) h
  simp only [smul_zero,smul_add,smul_smul,hs,one_zsmul] at hh
  rw [pow_succ,mul_neg_one,neg_smul]
  exact eq_neg_of_add_eq_zero_right hh.symm

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]

/-- The actual support cap has boundary sign (-1)^(a+1) on a genuine relative scalar cycle. -/
theorem supportCap_boundary_sign (S : Set B) (a b : ℕ)
    (x : (SingularLocalSupport.supportCochains p V S).X a)
    (c : (RationalManifoldCompact.supportChains S).X (a+b+1))
    (hc : (RationalManifoldCompact.supportChains S).d (a+b+1) (a+b) c = 0) :
    (SingularLocalHomology.localChains p hp.out V).d (b+1) b
      (SingularLocalCompactCap.supportCap p V S a (b+1) x c) =
    (-1 : ℤ)^(a+1) • SingularLocalCompactCap.supportCap p V S (a+1) b
      ((SingularLocalSupport.supportCochains p V S).d a (a+1) x)
      ((castLeft (RationalManifoldCompact.supportChains S) a b).hom c) :=
  cap_boundary_sign _ _ _ _ (SingularLocalCompactCap.supportCap_leibniz p V S) a b x c hc

end TernaryPoly.SingularLocalCompactCapMV
