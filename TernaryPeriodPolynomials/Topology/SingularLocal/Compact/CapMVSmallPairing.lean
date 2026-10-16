module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.CapMVKernelPairing

@[expose] public section


noncomputable section
namespace TernaryPoly.SingularLocalCompactCapMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open SingularLocalSupport SingularLocalCompactCap SingularLocalCompactMV SingularLocalCap

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G) [IsCancelSMul G E]
  (K L : Set B) (hK : IsClosed K) (hL : IsClosed L) (U D : Opens B) (hKU : K ⊆ U) (hLD : L ⊆ D)
  (hUD : U ⊔ D = ⊤)

/-- The actual ambient cap lies in the image of the genuine ordinary small-chain inclusion. -/
theorem ambientPairing_small (a b : ℕ) (x : (supportCochains p V (K ∪ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (cokernel.π (smallToLocal p V U D hUD)).f b
      (ambientPairing p V K L hK hL U D hKU hLD a b x c) = 0 := by
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective ((supportSum p V K L).f a)).mp inferInstance x
  rw [← hy,← middlePairing_sum p V K L hK hL U D hKU hLD hUD]
  exact congrArg (fun f => f ((ordinarySequence p V U D hUD).g.f b
    (middlePairing p V K L hK hL U D hKU hLD a b y c)))
      (HomologicalComplex.congr_hom (cokernel.condition (smallToLocal p V U D hUD)) b)

/-- The actual ambient support cap factors through genuine ordinary small local chains. -/
def smallPairing := exactLiftPairing (RelativeChainSequence.sequence (smallToLocal p V U D hUD))
  (RelativeChainSequence.shortExact (smallToLocal p V U D hUD)) (supportCochains p V (K ∪ L))
  (supportScalarSmall K L hK hL U D hKU hLD) (ambientPairing p V K L hK hL U D hKU hLD)
    (ambientPairing_small p V K L hK hL U D hKU hLD hUD)

/-- The actual small-chain cap obeys the geometric Leibniz convention. -/
theorem smallPairing_leibniz : Descent.Leibniz (supportCochains p V (K ∪ L))
    (supportScalarSmall K L hK hL U D hKU hLD) (ordinarySequence p V U D hUD).X₃
      (smallPairing p V K L hK hL U D hKU hLD hUD) :=
  exactLiftPairing_leibniz _ _ _ _ _ _ (ambientPairing_leibniz p V K L hK hL U D hKU hLD)

/-- Actual small inclusion sends the genuine small-chain cap to the literal ambient support cap. -/
theorem smallPairing_inclusion (a b : ℕ) (x : (supportCochains p V (K ∪ L)).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (smallToLocal p V U D hUD).f b (smallPairing p V K L hK hL U D hKU hLD hUD a b x c) =
      ambientPairing p V K L hK hL U D hKU hLD a b x c :=
  exactLiftPairing_inclusion (RelativeChainSequence.sequence (smallToLocal p V U D hUD))
    (RelativeChainSequence.shortExact (smallToLocal p V U D hUD)) _ _
    (ambientPairing p V K L hK hL U D hKU hLD)
    (ambientPairing_small p V K L hK hL U D hKU hLD hUD) a b x c

/-- The actual middle cap and small cap commute with the two genuine sum maps. -/
theorem smallPairing_sum (a b : ℕ) (x : (supportCochains p V K ⊞ supportCochains p V L).X a)
    (c : (supportScalarSmall K L hK hL U D hKU hLD).X (a+b)) :
    (ordinarySequence p V U D hUD).g.f b (middlePairing p V K L hK hL U D hKU hLD a b x c) =
      smallPairing p V K L hK hL U D hKU hLD hUD a b ((supportSum p V K L).f a x) c := by
  apply (ModuleCat.mono_iff_injective ((smallToLocal p V U D hUD).f b)).mp inferInstance
  rw [smallPairing_inclusion]
  exact middlePairing_sum p V K L hK hL U D hKU hLD hUD a b x c

end TernaryPoly.SingularLocalCompactCapMV
