module

public import TernaryPeriodPolynomials.Topology.SingularLocal.Compact.MVSmallEpi
public import TernaryPeriodPolynomials.Topology.Equivariant.Singular.MayerVietorisLocalMaps

@[expose] public section

noncomputable section
namespace TernaryPoly.SingularLocalCompactMV
open CategoryTheory Limits HomologicalComplex TopologicalSpace
open EquivariantSingularSmall EquivariantSingularMayerVietoris SingularLocalCoefficient

/-- A short exact sequence identifies its first term with the genuine kernel of its second map. -/
def shortExactKernelIso {C : Type*} [Category C] [Abelian C] (S : ShortComplex C) (hS : S.ShortExact) :
    S.X₁ ≅ kernel S.g := by
  have : Mono S.f := hS.mono_f
  exact {
    hom := kernel.lift S.g S.f S.zero
    inv := hS.exact.lift (kernel.ι S.g) (kernel.condition S.g)
    hom_inv_id := by
      apply (cancel_mono S.f).mp
      rw [Category.assoc,hS.exact.lift_f,kernel.lift_ι,Category.id_comp]
    inv_hom_id := by
      apply (cancel_mono (kernel.ι S.g)).mp
      rw [Category.assoc,kernel.lift_ι,hS.exact.lift_f,Category.id_comp] }

/-- This canonical short-exact kernel isomorphism retains the actual first map. -/
theorem shortExactKernelIso_inclusion {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    (shortExactKernelIso S hS).hom ≫ kernel.ι S.g = S.f := kernel.lift_ι _ _ _

variable {G : Type} [Group G] {E B : TopCat.{0}} [MulAction G E] [ContinuousConstSMul G E]
  (p : E ⟶ B) [hp : Fact (IsQuotientCoveringMap p G)] (V : Rep.{0} ℚ G)
  (A D : Opens B) (hAD : A ⊔ D = ⊤)

/-- Genuine local small-cochain restriction is degreewise epi for arbitrary rational coefficients. -/
instance localToSmall_epi : Epi (localToSmall p A D hAD V) := by
  unfold localToSmall
  infer_instance

/-- The actual local-cochain map to the kernel of the genuine Mayer–Vietoris difference map. -/
def coverKernelComparison : localCochains p hp.out V ⟶ kernel (localSmallSequence p A D hAD V).g :=
  localToSmall p A D hAD V ≫
    (shortExactKernelIso (localSmallSequence p A D hAD V) (localSmallSequence_shortExact p A D hAD V)).hom

/-- The kernel comparison is the pair of genuine open restrictions on ambient cochains. -/
theorem coverKernelComparison_inclusion :
    coverKernelComparison p V A D hAD ≫ kernel.ι (localSmallSequence p A D hAD V).g =
      biprod.lift (localRestriction p A V) (localRestriction p D V) := by
  let t : localCochains p hp.out V ⟶ (localSmallSequence p A D hAD V).X₁ := localToSmall p A D hAD V
  change (t ≫ (shortExactKernelIso (localSmallSequence p A D hAD V) _).hom) ≫ _ = _
  rw [Category.assoc,shortExactKernelIso_inclusion]
  exact localSmallSequence_f p A D hAD V

/-- The actual local Mayer–Vietoris kernel comparison is epi as a cochain map. -/
instance coverKernelComparison_epi : Epi (coverKernelComparison p V A D hAD) := by
  let t : localCochains p hp.out V ⟶ (localSmallSequence p A D hAD V).X₁ := localToSmall p A D hAD V
  have : Epi t := inferInstanceAs (Epi (localToSmall p A D hAD V))
  change Epi (t ≫ (shortExactKernelIso (localSmallSequence p A D hAD V) _).hom)
  infer_instance

/-- The actual local Mayer–Vietoris kernel comparison is a quasi-isomorphism in every degree. -/
instance coverKernelComparison_quasiIso : QuasiIso (coverKernelComparison p V A D hAD) := by
  let t : localCochains p hp.out V ⟶ (localSmallSequence p A D hAD V).X₁ := localToSmall p A D hAD V
  have : QuasiIso t := inferInstanceAs (QuasiIso (localToSmall p A D hAD V))
  change QuasiIso (t ≫ (shortExactKernelIso (localSmallSequence p A D hAD V) _).hom)
  infer_instance

end TernaryPoly.SingularLocalCompactMV
