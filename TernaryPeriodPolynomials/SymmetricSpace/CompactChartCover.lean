module

public import TernaryPeriodPolynomials.SymmetricSpace.Rational.LocalCompact
public import TernaryPeriodPolynomials.SymmetricSpace.Rational.GluingAction
public import TernaryPeriodPolynomials.SymmetricSpace.Arithmetic.SymmetricSpaceArithmeticProper

@[expose] public section


noncomputable section
namespace TernaryPoly.SymmetricSpaceCompactChartCover
open Topology SymmetricSpaceRationalGluing SymmetricSpaceFlagCoordinates
  SymmetricSpaceRationalAction SymmetricSpaceArithmeticProper

/-- Every compact subset of the actual gluing is covered by finitely many compact chart pieces. -/
theorem compact_chart_cover (C : Set Glued) (hC : IsCompact C) :
    ∃ I : Finset Glued, ∃ a : Glued → RationalGL, ∃ K : Glued → Set Corner,
      (∀ x, IsCompact (K x)) ∧ C ⊆ ⋃ x ∈ I, chart (a x) '' K x := by
  let := cornerLocallyCompact
  choose a p hp using chart_jointly_surjective
  choose K hK hN using fun x : Glued => exists_compact_mem_nhds (p x)
  have hneigh (x : Glued) : chart (a x) '' K x ∈ nhds x := by
    have h := (chart_isOpenEmbedding (a x)).isOpenMap.image_mem_nhds (hN x)
    rwa [hp x] at h
  obtain ⟨I,-,hcover⟩ := hC.elim_nhds_subcover _ (fun x _ => hneigh x)
  exact ⟨I,a,K,hK,hcover⟩

/-- The exact matrix finiteness obligation for two compact rational chart pieces. -/
def ChartTransporters (a b : RationalGL) (K L : Set Corner) : Set IntegralGL :=
  {g | ∃ p ∈ K, ∃ q ∈ L, integralAction g (chart a p) = chart b q}

/-- Finite compact-chart transporters imply the full actual arithmetic properness condition. -/
theorem finite_compact_transporters
    (hchart : ∀ a b K L, IsCompact K → IsCompact L → (ChartTransporters a b K L).Finite)
    (C D : Set Glued) (hC : IsCompact C) (hD : IsCompact D) :
    {g : IntegralGL | ((g • ·) '' C ∩ D).Nonempty}.Finite := by
  classical
  obtain ⟨I,a,K,hK,hcoverC⟩ := compact_chart_cover C hC
  obtain ⟨J,b,L,hL,hcoverD⟩ := compact_chart_cover D hD
  have hfin : (⋃ i ∈ I, ⋃ j ∈ J, ChartTransporters (a i) (b j) (K i) (L j)).Finite :=
    I.finite_toSet.biUnion fun i _ => J.finite_toSet.biUnion fun j _ =>
      hchart (a i) (b j) (K i) (L j) (hK i) (hL j)
  apply hfin.subset
  rintro g ⟨y,⟨x,hx,rfl⟩,hy⟩
  obtain ⟨i,hi,p,hp,hpx⟩ := Set.mem_iUnion₂.mp (hcoverC hx)
  obtain ⟨j,hj,q,hq,hqy⟩ := Set.mem_iUnion₂.mp (hcoverD hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨i,hi,Set.mem_iUnion₂.mpr ⟨j,hj,?_⟩⟩
  exact ⟨p,hp,q,hq,by rw [hpx]; exact hqy.symm⟩

end TernaryPoly.SymmetricSpaceCompactChartCover
