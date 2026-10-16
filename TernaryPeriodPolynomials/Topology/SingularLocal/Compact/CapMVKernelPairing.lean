module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVFixedPairingMaps
public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVLift

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV SingularLocalCap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)
  (hUD : U ⊔ D = ⊤)

/-- The actual middle cap of a kernel-of-sum cochain is killed by the actual ordinary sum. -/
theorem kernelPairing_zero (a b : ℕ) (x : (kernel (supportSum p V K L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (ordinarySequence p V U D hUD).g.f b
      (pullPairing (kernel.ι (supportSum p V K L)) (𝟙 _) (middlePairing p V K L hK hL U D hKU hLD) a b x c) = 0 := by
  apply (ModuleCat.mono_iff_injective ((smallToLocal p V U D hUD).f b)).mp inferInstance
  rw [map_zero]
  change ((ordinarySequence p V U D hUD).g ≫ smallToLocal p V U D hUD).f b
    (middlePairing p V K L hK hL U D hKU hLD a b ((kernel.ι (supportSum p V K L)).f a x) c) = 0
  erw [middlePairing_sum]
  have hx := congrArg (fun f => f x) (HomologicalComplex.congr_hom (kernel.condition (supportSum p V K L)) a)
  change (supportSum p V K L).f a ((kernel.ι (supportSum p V K L)).f a x) = 0 at hx
  rw [hx,map_zero,LinearMap.zero_apply]

/-- The genuine kernel-of-supportSum cap is obtained through actual ordinary-chain exactness. -/
def kernelPairing := exactLiftPairing (ordinarySequence p V U D hUD) (ordinarySequence_shortExact p V U D hUD)
  (kernel (supportSum p V K L)) (supportScalarSmall K L hK hL U D hKU hLD)
  (pullPairing (kernel.ι (supportSum p V K L)) (𝟙 _) (middlePairing p V K L hK hL U D hKU hLD))
    (kernelPairing_zero p V K L hK hL U D hKU hLD hUD)

/-- The genuine kernel cap satisfies the geometric Leibniz sign. -/
theorem kernelPairing_leibniz : Descent.Leibniz (kernel (supportSum p V K L))
    (supportScalarSmall K L hK hL U D hKU hLD) (ordinarySequence p V U D hUD).X₁
      (kernelPairing p V K L hK hL U D hKU hLD hUD) :=
  exactLiftPairing_leibniz _ _ _ _ _ _
    (pullPairing_leibniz _ _ _ (middlePairing_leibniz p V K L hK hL U D hKU hLD))

/-- The genuine kernel cap retains its literal actual middle-chain cap after inclusion. -/
theorem kernelPairing_inclusion (a b : ℕ) (x : (kernel (supportSum p V K L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (ordinarySequence p V U D hUD).f.f b (kernelPairing p V K L hK hL U D hKU hLD hUD a b x c) =
      middlePairing p V K L hK hL U D hKU hLD a b ((kernel.ι (supportSum p V K L)).f a x) c :=
  exactLiftPairing_inclusion _ _ _ _ _ _ a b x c

/-- The actual intersection-support comparison intertwines the genuine intersection cap and
the genuine kernel cap, before passing to the quasi-isomorphism on cohomology. -/
theorem kernelPairing_intersection (a b : ℕ) (x : (supportCochains p V (K ∩ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    kernelPairing p V K L hK hL U D hKU hLD hUD a b ((intersectionComparison p V K L).f a x) c =
      intersectionPairing p V K L hK hL U D hKU hLD a b x c := by
  have := (ordinarySequence_shortExact p V U D hUD).mono_f
  apply (ModuleCat.mono_iff_injective ((ordinarySequence p V U D hUD).f.f b)).mp inferInstance
  rw [kernelPairing_inclusion]
  have hx := congrArg (fun f => f x)
    (HomologicalComplex.congr_hom (intersectionComparison_inclusion p V K L) a)
  change (kernel.ι (supportSum p V K L)).f a ((intersectionComparison p V K L).f a x) =
    (supportDiagonal p V K L).f a x at hx
  rw [hx]
  exact (intersectionPairing_diagonal p V K L hK hL U D hKU hLD hUD a b x c).symm

end TernaryPoly.SingularLocalCompactCapMV
