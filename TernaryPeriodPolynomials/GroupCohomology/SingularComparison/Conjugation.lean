module

public import TernaryPeriodPolynomials.GroupCohomology.SingularComparison.Natural

@[expose] public section


/-!
# Homology bridge: naturality in conjugation

Formalized by Claude Sonnet 5.5.

For `g : G` and subgroups `Λ, Λ'` with `g Λ g⁻¹ ≤ Λ'`, `bridgeClass_conj` says that Mathlib's functoriality
map `groupHomology.map (conjIncl g hg) (phiConj g hg) (j+1)` for `γ ↦ gγg⁻¹ : Λ → Λ'` (trivial coefficients)
sends the class of a homogeneous cycle `c` modulo `Λ`-null chains to the class of its *left translate*
`leftTranslate g (j+1) c` modulo `Λ'`-null chains.  The proof follows `chains_conj_comm`,
generalized from a normal subgroup `N ◁ K` to `Λ → Λ'` in an ambient group, and uses `homologyMap_FNrt`
(right translation acts trivially on homology) to pass from the conjugation chain map to left translation.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HomologyBridge

open CategoryTheory Representation MonoidalCategory
open TernaryPeriodPolynomials.Argument.GroupHomology
open scoped Classical
open TernaryPeriodPolynomials.BoundaryDuality.TraceChains (NullChains)
open TernaryPeriodPolynomials.BoundaryDuality.ChainCalculus (Chains leftTranslate leftTranslate_single)

variable {G : Type} [Group G] {Λ' Λ : Subgroup G}

/-- Conjugation `γ ↦ g γ g⁻¹` from `Λ` to `Λ'`. -/
def conjIncl (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') : Λ →* Λ' where
  toFun γ := ⟨g * γ.1 * g⁻¹, hg _ γ.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

/-- The identity intertwiner for conjugation. -/
def phiConj (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') : Rep.res Λ.subtype (triv (G := G)) ⟶
    Rep.res (conjIncl g hg) (Rep.res Λ'.subtype (triv (G := G))) := 𝟙 _

/-- The action of `g` from `V_Λ` to `V_Λ'`. -/
def gamGenMap (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    Coinvariants (ρ.comp Λ.subtype) →ₗ[ℂ] Coinvariants (ρ.comp Λ'.subtype) :=
  Coinvariants.lift _ ((Coinvariants.mk (ρ.comp Λ'.subtype)) ∘ₗ ρ g) fun γ => LinearMap.ext fun v => by
    have e : ρ g (ρ γ.1 v) = (ρ.comp Λ'.subtype) ⟨g * γ.1 * g⁻¹, hg _ γ.2⟩ (ρ g v) := by
      change ρ g (ρ γ.1 v) = ρ (g * γ.1 * g⁻¹) (ρ g v)
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    change Coinvariants.mk (ρ.comp Λ'.subtype) (ρ g (ρ γ.1 v)) = Coinvariants.mk _ (ρ g v)
    rw [e]
    exact Coinvariants.mk_self_apply (ρ.comp Λ'.subtype) _ _

@[simp] theorem gamGenMap_mk (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ G V) (v : V) :
    gamGenMap g hg ρ (Coinvariants.mk _ v) = Coinvariants.mk _ (ρ g v) := rfl

/-- The natural transformation `cN Λ ⟶ cN Λ'`. -/
def gamGenNat (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') : cN (k := ℂ) Λ ⟶ cN Λ' where
  app P := ModuleCat.ofHom (gamGenMap g hg P.ρ)
  naturality P Q f := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => by
    have h : f.hom (P.ρ g (v : P.V)) = Q.ρ g (f.hom (v : P.V)) :=
      Rep.hom_comm_apply f g (v : P.V)
    exact congrArg (Coinvariants.mk (Q.ρ.comp Λ'.subtype)) h.symm))

/-- The induced chain map on coinvariant complexes. -/
def GG (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (Y : ChainComplex (Rep ℂ G) ℕ) :
    CxN Λ Y ⟶ CxN Λ' Y :=
  (NatTrans.mapHomologicalComplex (gamGenNat g hg) _).app Y

theorem chains_conj_comm_gen (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') :
    groupHomology.chainsMap (conjIncl g hg) (phiConj g hg) ≫ betaA Λ' (triv (G := G)) =
      betaA Λ (triv (G := G)) ≫ GG g hg (YA (triv (G := G))) ≫ FNrt Λ' (triv (G := G)) g⁻¹ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun x => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun a => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, Finsupp.lsingle_apply]
  have eL : ((groupHomology.chainsMap (conjIncl g hg) (phiConj g hg)).f n).hom (Finsupp.single x a) =
      Finsupp.single (conjIncl g hg ∘ x) a := by
    have := groupHomology.chainsMap_f_single (conjIncl g hg) (phiConj g hg) n x
      (show ↑(Rep.res Λ.subtype (triv (G := G))) from a)
    exact this
  change ((betaA Λ' (triv (G := G))).f n).hom (((groupHomology.chainsMap (conjIncl g hg) (phiConj g hg)).f n).hom
      (Finsupp.single x a)) = ((FNrt Λ' (triv (G := G)) g⁻¹).f n).hom (((GG g hg (YA (triv (G := G)))).f n).hom
        (((betaA Λ (triv (G := G))).f n).hom (Finsupp.single x a)))
  rw [eL, betaA_single Λ' (triv (G := G)) n _, betaA_single Λ (triv (G := G)) n x]
  change _ = (cN (k := ℂ) Λ').map ((tensorLeft (triv (G := G))).map (rtTerm (k := ℂ) g⁻¹ n))
    (gamGenMap g hg ((triv (G := G)) ⊗ Rep.free ℂ G (Fin n → G)).ρ
      (Representation.Coinvariants.mk _ (a ⊗ₜ[ℂ] Finsupp.single (Λ.subtype ∘ x)
        (MonoidAlgebra.single (1 : G) (1 : ℂ)))))
  have hG : gamGenMap g hg ((triv (G := G)) ⊗ Rep.free ℂ G (Fin n → G)).ρ
      (Representation.Coinvariants.mk _ (a ⊗ₜ[ℂ] Finsupp.single (Λ.subtype ∘ x)
        (MonoidAlgebra.single (1 : G) (1 : ℂ)))) =
      Representation.Coinvariants.mk _ ((triv (G := G)).ρ g a ⊗ₜ[ℂ]
        (Rep.free ℂ G (Fin n → G)).ρ g (Finsupp.single (Λ.subtype ∘ x)
          (MonoidAlgebra.single (1 : G) (1 : ℂ)))) := rfl
  have hF := cN_tensorLeft_mk Λ' (triv (G := G)) (rtTerm (k := ℂ) g⁻¹ n) ((triv (G := G)).ρ g a)
    ((Rep.free ℂ G (Fin n → G)).ρ g (Finsupp.single (Λ.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : ℂ))))
  have e : (rtTerm (k := ℂ) g⁻¹ n).hom ((Rep.free ℂ G (Fin n → G)).ρ g
      (Finsupp.single (Λ.subtype ∘ x) (MonoidAlgebra.single (1 : G) (1 : ℂ)))) =
      Finsupp.single (Λ'.subtype ∘ conjIncl g hg ∘ x) (MonoidAlgebra.single (1 : G) (1 : ℂ)) := by
    change (rtTerm (k := ℂ) g⁻¹ n).hom
      ((Representation.free ℂ G (Fin n → G)) g (Finsupp.single (Λ.subtype ∘ x) (MonoidAlgebra.single 1 1))) = _
    rw [Representation.free_single_single, rtTerm_single]
    congr 1
    · funext i
      simp [conjIncl, conjInv_apply, mul_assoc]
    · simp
  refine Eq.trans ?_ ((congrArg (fun z => (cN (k := ℂ) Λ').map ((tensorLeft (triv (G := G))).map
    (rtTerm (k := ℂ) g⁻¹ n)) z) hG).trans hF).symm
  exact (congrArg (fun z => Representation.Coinvariants.mk _ (((triv (G := G)).ρ g a) ⊗ₜ[ℂ] z)) e).symm

theorem conj_comparison_gen (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (n : ℕ) :
    groupHomology.map (conjIncl g hg) (phiConj g hg) n ≫ (eN Λ' (triv (G := G)) n).hom =
      (eN Λ (triv (G := G)) n).hom ≫
        HomologicalComplex.homologyMap (GG g hg (YA (triv (G := G)))) n := by
  have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chains_conj_comm_gen g hg)
  have hA := HomologicalComplex.homologyMap_comp
    (groupHomology.chainsMap (conjIncl g hg) (phiConj g hg)) (betaA Λ' (triv (G := G))) n
  have hC : HomologicalComplex.homologyMap (betaA Λ (triv (G := G)) ≫ GG g hg (YA (triv (G := G))) ≫
      FNrt Λ' (triv (G := G)) g⁻¹) n =
      HomologicalComplex.homologyMap (betaA Λ (triv (G := G))) n ≫
        HomologicalComplex.homologyMap (GG g hg (YA (triv (G := G)))) n := by
    have c1 := HomologicalComplex.homologyMap_comp (betaA Λ (triv (G := G)))
      (GG g hg (YA (triv (G := G))) ≫ FNrt Λ' (triv (G := G)) g⁻¹) n
    have c2 := HomologicalComplex.homologyMap_comp (GG g hg (YA (triv (G := G))))
      (FNrt Λ' (triv (G := G)) g⁻¹) n
    have c3 := homologyMap_FNrt Λ' (triv (G := G)) g⁻¹ n
    refine c1.trans (congrArg (fun z => HomologicalComplex.homologyMap (betaA Λ (triv (G := G))) n ≫ z)
      (c2.trans ((congrArg (fun z => HomologicalComplex.homologyMap (GG g hg (YA (triv (G := G)))) n ≫ z) c3).trans
        (Category.comp_id _))))
  rw [eN_hom, eN_hom]
  exact hA.symm.trans (h1.trans hC)

/-- The chain map `Cstd Λ ⟶ Cstd Λ'` induced by left translation by `g`. -/
def GGs (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') : Cstd Λ ⟶ Cstd Λ' :=
  GG g hg (Ystd (G := G))

theorem isoCx_conj (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') :
    (isoCx Λ).hom ≫ GG g hg (YA (triv (G := G))) = GGs g hg ≫ (isoCx Λ').hom :=
  (NatTrans.mapHomologicalComplex (gamGenNat g hg) (ComplexShape.down ℕ)).naturality _

theorem gIso_conj_natural (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (n : ℕ) :
    (gIso Λ n).inv ≫ groupHomology.map (conjIncl g hg) (phiConj g hg) n ≫ (gIso Λ' n).hom =
      HomologicalComplex.homologyMap (GGs g hg) n := by
  have e1 := conj_comparison_gen g hg n
  simp only [gIso, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
    HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_inv, Category.assoc]
  rw [reassoc_of% e1, Iso.inv_hom_id_assoc, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [← Category.assoc, isoCx_conj, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem leftTranslate_eq_actC (g : G) (n : ℕ) : leftTranslate g n = actC g n := rfl

theorem sigma_conj (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (n : ℕ) (c : Chains G n) :
    ((GGs g hg).f n).hom (sigma Λ n c) = sigma Λ' n (leftTranslate g n c) := by
  rw [leftTranslate_eq_actC, sigma_apply, sigma_apply, toMA_actC]
  rfl

theorem boundary_leftTranslate (g : G) (n : ℕ) (c : Chains G (n + 1)) :
    TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (n + 1)
        (leftTranslate g (n + 1) c) =
      leftTranslate g n (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary
        (n + 1) c) := by
  apply (toMA n).injective
  rw [leftTranslate_eq_actC, leftTranslate_eq_actC, toMA_actC, ← toMA_boundary, ← toMA_boundary,
    toMA_actC]
  exact (Rep.hom_comm_apply ((Rep.standardComplex ℂ G).d (n + 1) n) g (toMA (n + 1) c))

theorem null_leftTranslate (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (n : ℕ) {c : Chains G n}
    (hc : c ∈ NullChains Λ n) : leftTranslate g n c ∈ NullChains Λ' n := by
  have : NullChains Λ n ≤ (NullChains Λ' n).comap (leftTranslate g n) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨γ, x, rfl⟩
    refine Submodule.mem_comap.mpr ?_
    rw [map_sub, leftTranslate_single, leftTranslate_single]
    have : Finsupp.single (fun i => g * (γ.1 * x i)) (1 : ℂ) - Finsupp.single (fun i => g * x i) 1 =
      Finsupp.single (fun i => (g * γ.1 * g⁻¹) * (g * x i)) 1 - Finsupp.single (fun i => g * x i) 1 := by
      congr 2
      funext i
      group
    refine Eq.subst (motive := fun z => z ∈ NullChains Λ' n) this.symm ?_
    exact Submodule.subset_span ⟨⟨g * γ.1 * g⁻¹, hg _ γ.2⟩, fun i => g * x i, rfl⟩
  exact this hc

theorem Zhom_leftTranslate (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (j : ℕ) {c : Chains G (j + 1)}
    (hc : c ∈ Zhom Λ j) : leftTranslate g (j + 1) c ∈ Zhom Λ' j := by
  rw [mem_Zhom] at hc ⊢
  rw [boundary_leftTranslate]
  exact null_leftTranslate g hg j hc

/-- The morphism of short complexes induced by left translation by `g`. -/
def SjConj (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (j : ℕ) : Sj Λ j ⟶ Sj Λ' j :=
  (HomologicalComplex.shortComplexFunctor' (ModuleCat ℂ) (ComplexShape.down ℕ) (j + 2) (j + 1) j).map
    (GGs g hg)

theorem bridgeClass_conj (g : G) (hg : ∀ γ ∈ Λ, g * γ * g⁻¹ ∈ Λ') (j : ℕ) (c : Zhom Λ j) :
    (groupHomology.map (conjIncl g hg) (phiConj g hg) (j + 1)).hom (bridgeClass Λ j c) =
      bridgeClass Λ' j ⟨leftTranslate g (j + 1) c.1, Zhom_leftTranslate g hg j c.2⟩ := by
  apply (ModuleCat.mono_iff_injective (gIso Λ' (j + 1)).hom).mp inferInstance
  set v := (homIsoSj Λ j).inv.hom (coverClass (sj_h₂ Λ j) c) with hv
  have hb : bridgeClass Λ j c = (gIso Λ (j + 1)).inv.hom v := rfl
  have hnat := congrArg (fun t => t.hom v) (gIso_conj_natural g hg (j + 1))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  have hcov := coverClass_natural (SjConj g hg j) (σ₂ := sigma Λ (j + 1))
    (σ₂' := (sigma Λ' (j + 1)) ∘ₗ leftTranslate g (j + 1))
    (σ₃ := sigma Λ j) (σ₃' := (sigma Λ' j) ∘ₗ leftTranslate g j)
    (d₂ := TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary (j + 1))
    (fun m => sigma_conj g hg (j + 1) m) (fun m => sigma_conj g hg j m)
    (sj_h₂ Λ j)
    (fun m => by
      change (Sj Λ' j).g.hom (sigma Λ' (j + 1) (leftTranslate g (j + 1) m)) =
        sigma Λ' j (leftTranslate g j (TernaryPeriodPolynomials.TopVanishing.homogeneousBoundary
          (j + 1) m))
      rw [← boundary_leftTranslate]
      exact sj_h₂ Λ' j _) c
  have hiso := congrArg (fun t => t.hom (coverClass (sj_h₂ Λ j) c))
    (homologyIsoSc'_inv_natural (GGs g hg) j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hiso
  rw [hb, hnat]
  change _ = (gIso Λ' (j + 1)).hom.hom ((gIso Λ' (j + 1)).inv.hom
    ((homIsoSj Λ' j).inv.hom (coverClass (sj_h₂ Λ' j)
      ⟨leftTranslate g (j + 1) c.1, Zhom_leftTranslate g hg j c.2⟩)))
  rw [Iso.inv_hom_id_apply]
  rw [hv]
  refine hiso.trans ?_
  exact congrArg (fun z => (homIsoSj Λ' j).inv.hom z) hcov

end TernaryPeriodPolynomials.Argument.HomologyBridge
