module

public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Relative.ChainsKernel
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Apartment.Generation
public import TernaryPeriodPolynomials.Building.Good.ApartmentEquivariance

@[expose] public section


noncomputable section
namespace TernaryPoly.OrdinaryApartmentPresentation
open ModThreeGoodAction AugmentedFrameComplex GoodRelativeChains OrientedListChains
open OrdinaryRelativeChains OrdinaryApartmentSpanComparison
local instance : DecidableEq RationalLine := Classical.decEq _

/-- Every actual ambient triangle is proper or has an ordered integral frame representative. -/
theorem ambient_triangle_cases (l : List RationalLine) (hlen : l.length=3)
    (hl : Allowed ambient l) : l.toFinset∈properAmbient ∨ ∃ g : IntegralGL,triangleList g=l := by
  obtain ⟨L,M,N,rfl⟩ := List.length_eq_three.mp hlen
  have hg : [L,M,N].toFinset∈ambient := hl.resolve_left (by simp)
  by_cases hd : Module.finrank ℚ (faceSpan [L,M,N].toFinset)≤2
  · exact Or.inl ⟨hg,hd⟩
  · right
    have hle : Module.finrank ℚ (faceSpan [L,M,N].toFinset)≤3 := by
      simpa only [Space,Module.finrank_pi,Module.finrank_self,Finset.sum_const,
        Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using
        Submodule.finrank_le (faceSpan [L,M,N].toFinset)
    have he : Module.finrank ℚ (faceSpan [L,M,N].toFinset)=3 := by omega
    have hi : @Finset.image (Fin 3) RationalLine (fun a b => Subtype.instDecidableEq a b)
        (![L,M,N] : Fin 3 → RationalLine) Finset.univ=[L,M,N].toFinset := by
      ext x
      simp [Fin.exists_fin_succ,eq_comm]
    obtain ⟨g,hgL⟩ := AmbientIndependentTriple.exists_integralGL_of_finrank_eq_three ![L,M,N]
      (by rwa [hi]) (by rwa [hi])
    refine ⟨g,?_⟩
    have h0 : augmentedLine g 0=L := hgL 0
    have h1 : augmentedLine g 1=M := hgL 1
    have h2 : augmentedLine g 2=N := hgL 2
    simp only [triangleList,h0,h1,h2]

/-- Values on integral frame triangles determine a functional on the actual relative quotient. -/
theorem relative_functional_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    (f g : OrdinaryRelativeChains.RelativeBoundaryTwo →ₗ[ℚ] E)
    (h : ∀ a : IntegralGL,f (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle a))=
      g (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle a))) : f=g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := OrdinaryRelativeChains.nullSubmodule.mkQ_surjective x
  obtain ⟨c,hc⟩ := c
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨l,hlen,hl,rfl⟩ := hc
    have hm : simplex l∈AmbientTwo := by simpa only [hlen] using simplex_mem_chains ambient l hl
    rcases ambient_triangle_cases l hlen hl with hp | ⟨a,ha⟩
    · have hpm : simplex l∈chains properAmbient 3 := by
        simpa only [hlen] using simplex_mem_chains properAmbient l (Or.inr hp)
      have hz : OrdinaryRelativeChains.quotientMap (⟨simplex l,hm⟩ : AmbientTwo)=0 :=
        OrdinaryRelativeChains.quotientMap_proper ⟨simplex l,hpm⟩
      change f (OrdinaryRelativeChains.quotientMap (⟨simplex l,hm⟩ : AmbientTwo))=
        g (OrdinaryRelativeChains.quotientMap (⟨simplex l,hm⟩ : AmbientTwo))
      rw [hz,map_zero,map_zero]
    · have ht : OrdinaryRelativeChains.triangle a=(⟨simplex l,hm⟩ : AmbientTwo) := by
        apply Subtype.ext
        change simplex (triangleList a)=simplex l
        rw [ha]
      exact ht ▸ h a
  | zero =>
    change f (OrdinaryRelativeChains.nullSubmodule.mkQ (0 : AmbientTwo))=
      g (OrdinaryRelativeChains.nullSubmodule.mkQ (0 : AmbientTwo))
    rw [map_zero,map_zero,map_zero]
  | add c d hc hd ihc ihd =>
    change f (OrdinaryRelativeChains.nullSubmodule.mkQ ((⟨c,hc⟩ : AmbientTwo)+⟨d,hd⟩))=
      g (OrdinaryRelativeChains.nullSubmodule.mkQ ((⟨c,hc⟩ : AmbientTwo)+⟨d,hd⟩))
    simp only [map_add,ihc,ihd]
  | smul q c hc ih =>
    change f (OrdinaryRelativeChains.nullSubmodule.mkQ (q • (⟨c,hc⟩ : AmbientTwo)))=
      g (OrdinaryRelativeChains.nullSubmodule.mkQ (q • (⟨c,hc⟩ : AmbientTwo)))
    simp only [map_smul,ih]

/-- The genuine unrestricted ambient relative quotient is the ordinary incidence cycle module. -/
def presentation : OrdinaryRelativeChains.RelativeBoundaryTwo ≃ₗ[ℚ] OrdinaryIncidenceChains.Cycles :=
  LinearEquiv.ofBijective comparison
    ⟨OrdinaryRelativeChainsKernel.comparison_injective,OrdinaryApartmentGeneration.comparison_surjective⟩

/-- The actual ordinary apartment cycle belonging to an arbitrary integral frame. -/
def frameCycle (g : IntegralGL) : OrdinaryIncidenceChains.Cycles :=
  comparison (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g))

@[simp] theorem presentation_triangle (g : IntegralGL) :
    presentation (OrdinaryRelativeChains.quotientMap (OrdinaryRelativeChains.triangle g))=frameCycle g := rfl

theorem frameCycle_apartment (g : IntegralGL) : frameCycle g=
    GoodApartmentCycles.apartmentCycle (fun _ => True) (line (augmentedLine g 0))
      (line (augmentedLine g 1)) (line (augmentedLine g 2)) :=
  OrdinaryApartmentGeneration.comparison_triangle g

/-- Agreement on all integral ordinary apartments determines the entire cycle functional. -/
theorem cycle_functional_ext {E : Type*} [AddCommGroup E] [Module ℚ E]
    (f g : OrdinaryIncidenceChains.Cycles →ₗ[ℚ] E)
    (h : ∀ a : IntegralGL,f (frameCycle a)=g (frameCycle a)) : f=g := by
  have he : f.comp comparison=g.comp comparison := relative_functional_ext _ _ h
  apply LinearMap.ext
  intro c
  obtain ⟨x,rfl⟩ := OrdinaryApartmentGeneration.comparison_surjective c
  exact LinearMap.congr_fun he x

theorem line_action (k : K) (L : RationalLine) :
    OrdinaryIncidence.lineAction k (line L)=line (AugmentedChainAction.lineAction k.val L) := rfl

/-- The actual incidence action carries each integral apartment to the product frame. -/
theorem frameCycle_equivariant (k : K) (g : IntegralGL) :
    OrdinaryIncidenceChains.complex.cyclesAction k (frameCycle g)=frameCycle (k.val*g) := by
  rw [frameCycle_apartment,frameCycle_apartment]
  apply Subtype.ext
  have he := GoodApartmentCycles.apartmentChainEquiv_apartment (fun _ => True)
    (GoodBuilding.subspaceEquiv k) (ModThreeGoodAction.act_finrank k) (fun _ => Iff.rfl)
    (line (augmentedLine g 0)) (line (augmentedLine g 1)) (line (augmentedLine g 2))
  change OrdinaryIncidenceChains.edgeRepresentation k
    (GoodApartmentCycles.apartmentChain (fun _ => True) (line (augmentedLine g 0))
      (line (augmentedLine g 1)) (line (augmentedLine g 2)))=
    GoodApartmentCycles.apartmentChain (fun _ => True)
      (OrdinaryIncidence.lineAction k (line (augmentedLine g 0)))
      (OrdinaryIncidence.lineAction k (line (augmentedLine g 1)))
      (OrdinaryIncidence.lineAction k (line (augmentedLine g 2))) at he
  rw [line_action,line_action,line_action,AugmentedChainAction.lineAction_augmentedLine,
    AugmentedChainAction.lineAction_augmentedLine,AugmentedChainAction.lineAction_augmentedLine] at he
  exact he

end TernaryPoly.OrdinaryApartmentPresentation
