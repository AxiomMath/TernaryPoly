module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Bridge

@[expose] public section


/-!
# Homology bridge: naturality in the subgroup

Formalized by Claude Sonnet 5.5.

For `Λ' ≤ Λ ≤ G`, `bridgeClass_natural` says that Mathlib's corestriction
`groupHomology.map (Subgroup.inclusion h) (phiInc h) (j+1)` applied to the class of a homogeneous cycle
modulo `Λ'`-null chains is the class of the same chain modulo `Λ`-null chains.  The proof compares the
chain maps `chainsMap incl ≫ betaA Λ = betaA Λ' ≫ QG` (`chains_incl_comm_gen`), then the isomorphisms `gIso`.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology
open scoped Classical
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains)

variable {G : Type} [Group G] {Λ' Λ : Subgroup G}

/-- The quotient `V_{Λ'} → V_Λ` for `Λ' ≤ Λ`. -/
def qGenMap (h : Λ' ≤ Λ) {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) :
    Coinvariants (ρ.comp Λ'.subtype) →ₗ[ℂ] Coinvariants (ρ.comp Λ.subtype) :=
  Coinvariants.lift _ (Coinvariants.mk _) fun γ => LinearMap.ext fun v =>
    Coinvariants.mk_self_apply (ρ.comp Λ.subtype) ⟨γ.1, h γ.2⟩ v

/-- The quotient natural transformation `cN Λ' ⟶ cN Λ`. -/
def qGenNat (h : Λ' ≤ Λ) : cN (k := ℂ) Λ' ⟶ cN Λ where
  app P := ModuleCat.ofHom (qGenMap h P.ρ)
  naturality _ _ _ := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))

/-- The induced chain map on coinvariant complexes. -/
def QG (h : Λ' ≤ Λ) (Y : ChainComplex (Rep ℂ G) ℕ) : CxN Λ' Y ⟶ CxN Λ Y :=
  (NatTrans.mapHomologicalComplex (qGenNat h) _).app Y

/-- The identity intertwiner for the inclusion of subgroups. -/
def phiInc (h : Λ' ≤ Λ) : Rep.res Λ'.subtype (triv (G := G)) ⟶
    Rep.res (Subgroup.inclusion h) (Rep.res Λ.subtype (triv (G := G))) := 𝟙 _

theorem chains_incl_comm_gen (h : Λ' ≤ Λ) :
    groupHomology.chainsMap (Subgroup.inclusion h) (phiInc h) ≫
        betaA Λ (triv (G := G)) =
      betaA Λ' (triv (G := G)) ≫ QG h (YA (triv (G := G))) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom]
  have eL := groupHomology.chainsMap_f_single (Subgroup.inclusion h) (phiInc h) n x
    (show ↑(Rep.res Λ'.subtype (triv (G := G))) from a)
  simp only [Finsupp.lsingle_apply]
  have e5 : ((betaA Λ' (triv (G := G)) ≫ QG h (YA (triv (G := G)))).f n).hom
        (Finsupp.single x a) =
      ((QG h (YA (triv (G := G)))).f n).hom (((betaA Λ' (triv (G := G))).f n).hom
        (Finsupp.single x a)) := rfl
  refine Eq.trans ?_ e5.symm
  rw [eL, betaA_single Λ (triv (G := G)) n (Subgroup.inclusion h ∘ x),
    betaA_single Λ' (triv (G := G)) n x]
  rfl

theorem eN_incl_comparison (h : Λ' ≤ Λ) (n : ℕ) :
    groupHomology.map (Subgroup.inclusion h) (phiInc h) n ≫ (eN Λ (triv (G := G)) n).hom =
      (eN Λ' (triv (G := G)) n).hom ≫
        HomologicalComplex.homologyMap (QG h (YA (triv (G := G)))) n := by
  have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (chains_incl_comm_gen (G := G) h)
  have hA := HomologicalComplex.homologyMap_comp
    (groupHomology.chainsMap (Subgroup.inclusion h) (phiInc h)) (betaA Λ (triv (G := G))) n
  have hB := HomologicalComplex.homologyMap_comp (betaA Λ' (triv (G := G)))
    (QG h (YA (triv (G := G)))) n
  rw [eN_hom, eN_hom]
  exact hA.symm.trans (h1.trans hB)

theorem homologyMap_homologyIsoSc' {K L : ChainComplex (ModuleCat ℂ) ℕ} (f : K ⟶ L) (j : ℕ) :
    HomologicalComplex.homologyMap f (j + 1) ≫
        (L.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).hom =
      (K.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).hom ≫
        ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ)
          (ComplexShape.down ℕ) (j + 2) (j + 1) j).map f) :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat ℂ) (ComplexShape.down ℕ) (j + 2) (j + 1) j
    (ChainComplex.prev ℕ (j + 1)) (ChainComplex.next_nat_succ j)).hom.naturality f

theorem isoCx_natural (h : Λ' ≤ Λ) :
    (isoCx Λ').hom ≫ QG h (YA (triv (G := G))) = QG h (Ystd (G := G)) ≫ (isoCx Λ).hom :=
  (NatTrans.mapHomologicalComplex (qGenNat h) (ComplexShape.down ℕ)).naturality _

theorem gIso_incl_natural (h : Λ' ≤ Λ) (n : ℕ) :
    (gIso Λ' n).inv ≫ groupHomology.map (Subgroup.inclusion h) (phiInc h) n ≫ (gIso Λ n).hom =
      HomologicalComplex.homologyMap (QG h (Ystd (G := G))) n := by
  have e1 := eN_incl_comparison (G := G) h n
  have e2 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (isoCx_natural h)
  have e3 := HomologicalComplex.homologyMap_comp (isoCx Λ').hom (QG h (YA (triv (G := G)))) n
  have e4 := HomologicalComplex.homologyMap_comp (QG h (Ystd (G := G))) (isoCx Λ).hom n
  simp only [gIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv, Category.assoc]
  rw [reassoc_of% e1, Iso.inv_hom_id_assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [← Category.assoc, isoCx_natural h, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem homologyIsoSc'_inv_natural {K L : ChainComplex (ModuleCat ℂ) ℕ} (f : K ⟶ L) (j : ℕ) :
    (K.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).inv ≫ HomologicalComplex.homologyMap f (j + 1) =
      ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ)
          (ComplexShape.down ℕ) (j + 2) (j + 1) j).map f) ≫
        (L.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).inv := by
  calc _ = (K.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).inv ≫ (HomologicalComplex.homologyMap f (j + 1) ≫
          (L.homologyIsoSc' (j + 2) (j + 1) j (ChainComplex.prev ℕ (j + 1))
          (ChainComplex.next_nat_succ j)).hom) ≫ (L.homologyIsoSc' (j + 2) (j + 1) j
          (ChainComplex.prev ℕ (j + 1)) (ChainComplex.next_nat_succ j)).inv := by simp
    _ = _ := by rw [homologyMap_homologyIsoSc' f j]; simp

theorem null_mono (h : Λ' ≤ Λ) (n : ℕ) : NullChains Λ' n ≤ NullChains Λ n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨γ, x, rfl⟩
  exact Submodule.subset_span ⟨⟨γ.1, h γ.2⟩, x, rfl⟩

theorem Zhom_mono (h : Λ' ≤ Λ) (j : ℕ) : Zhom Λ' j ≤ Zhom Λ j := by
  intro c hc
  rw [mem_Zhom] at hc ⊢
  exact null_mono h j hc

/-- The morphism of short complexes induced by `Λ' ≤ Λ`. -/
def SjMap (h : Λ' ≤ Λ) (j : ℕ) : Sj Λ' j ⟶ Sj Λ j :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ) (ComplexShape.down ℕ) (j + 2) (j + 1) j).map
    (QG h (Ystd (G := G)))

theorem sigma_natural (h : Λ' ≤ Λ) (n : ℕ) (c : Chains G n) :
    ((QG h (Ystd (G := G))).f n).hom (sigma Λ' n c) = sigma Λ n c := rfl

theorem bridgeClass_natural (h : Λ' ≤ Λ) (j : ℕ) (c : Zhom Λ' j) :
    (groupHomology.map (Subgroup.inclusion h) (phiInc h) (j + 1)).hom (bridgeClass Λ' j c) =
      bridgeClass Λ j ⟨c.1, Zhom_mono h j c.2⟩ := by
  apply (ModuleCat.mono_iff_injective (gIso Λ (j + 1)).hom).mp inferInstance
  set v := (homIsoSj Λ' j).inv.hom (coverClass (sj_h₂ Λ' j) c) with hv
  have hb : bridgeClass Λ' j c = (gIso Λ' (j + 1)).inv.hom v := rfl
  have hnat := congrArg (fun t => t.hom v) (gIso_incl_natural h (j + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  have hcov := coverClass_natural (SjMap h j) (σ₂ := sigma Λ' (j + 1)) (σ₂' := sigma Λ (j + 1))
    (σ₃ := sigma Λ' j) (σ₃' := sigma Λ j) (d₂ := TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (j + 1))
    (fun m => sigma_natural h (j + 1) m) (fun m => sigma_natural h j m)
    (sj_h₂ Λ' j) (sj_h₂ Λ j) c
  have hiso := congrArg (fun t => t.hom (coverClass (sj_h₂ Λ' j) c))
    (homologyIsoSc'_inv_natural (QG h (Ystd (G := G))) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hiso
  rw [hb, hnat]
  have hfin : ∀ X : ↑(HomologicalComplex.homology (Cstd Λ) (j + 1)),
      (gIso Λ (j + 1)).hom.hom ((gIso Λ (j + 1)).inv.hom X) = X := fun X =>
    Iso.inv_hom_id_apply _ _
  change _ = (gIso Λ (j + 1)).hom.hom ((gIso Λ (j + 1)).inv.hom
    ((homIsoSj Λ j).inv.hom (coverClass (sj_h₂ Λ j) ⟨c.1, Zhom_mono h j c.2⟩)))
  rw [hfin, ← hcov]
  exact hiso

end TernaryPeriodPolynomials.Argument.HomologyBridge
