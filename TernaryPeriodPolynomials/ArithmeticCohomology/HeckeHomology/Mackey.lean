module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.Hecke

@[expose] public section


/-!
# Mackey's formula for the coset-sum transfer on coinvariants

Formalized by Claude Sonnet 5.5.
-/

open CategoryTheory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open scoped Classical

variable {Γ : Type} [Group Γ] (P S : Subgroup Γ)

/-- `x⁻¹ S x`. -/
def conjSub (x : Γ) : Subgroup Γ := S.comap (MulAut.conj x).toMonoidHom

theorem mem_conjSub {x : Γ} {y : Γ} : y ∈ conjSub S x ↔ x * y * x⁻¹ ∈ S := Iff.rfl

instance finiteIndex_conjSub [S.FiniteIndex] (x : Γ) : (conjSub S x).FiniteIndex := by
  refine ⟨?_⟩
  unfold conjSub
  rw [Subgroup.index_comap_of_surjective _ (MulAut.conj x).surjective]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- `P ∩ x⁻¹ S x` as a subgroup of `P`. -/
def Sx (x : Γ) : Subgroup P := (conjSub S x).subgroupOf P

theorem mem_Sx {x : Γ} {p : P} : p ∈ Sx P S x ↔ x * (p : Γ) * x⁻¹ ∈ S := Iff.rfl

instance finiteIndex_Sx [S.FiniteIndex] (x : Γ) : (Sx P S x).FiniteIndex := by
  unfold Sx; infer_instance


section Coinv

variable {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k Γ V)

/-- The action of `x` as a map `V_{P ∩ x⁻¹ S x} → V_S`. -/
def actMapX (x : Γ) : Coinvariants ((ρ.comp P.subtype).comp (Sx P S x).subtype) →ₗ[k]
    Coinvariants (ρ.comp S.subtype) :=
  Coinvariants.lift _ ((Coinvariants.mk (ρ.comp S.subtype)).comp (ρ x)) (fun h => LinearMap.ext fun v => by
    have hh : x * ((h : P) : Γ) * x⁻¹ ∈ S := h.2
    have e : ρ x (ρ (((h : P) : Γ)) v) = ρ (x * ((h : P) : Γ) * x⁻¹) (ρ x v) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    change Coinvariants.mk (ρ.comp S.subtype) (ρ x (ρ (((h : P) : Γ)) v)) =
      Coinvariants.mk (ρ.comp S.subtype) (ρ x v)
    rw [e]
    exact Coinvariants.mk_self_apply (ρ.comp S.subtype) ⟨_, hh⟩ (ρ x v))

theorem actMapX_mk (x : Γ) (v : V) :
    actMapX P S ρ x (Coinvariants.mk _ v) = Coinvariants.mk (ρ.comp S.subtype) (ρ x v) := rfl

variable [S.FiniteIndex]

/-- The set `X` is a complete set of representatives of the double cosets `S \ Γ / P`. -/
structure DoubleCosetReps (X : Finset Γ) : Prop where
  cover : ∀ y : Γ, ∃ x ∈ X, ∃ s ∈ S, ∃ p ∈ P, y = s * x * p
  disjoint : ∀ x ∈ X, ∀ x' ∈ X, ∀ s ∈ S, ∀ s' ∈ S, ∀ p ∈ P, ∀ p' ∈ P, s * x * p = s' * x' * p' → x = x'

/-- **Mackey, coset form.** -/
theorem tSumR_mackey {X : Finset Γ} (hX : DoubleCosetReps P S X) (v : V) :
    tSumR S ρ v = ∑ x ∈ X, ∑ q : RC (Sx P S x),
      Coinvariants.mk (ρ.comp S.subtype) (ρ (x * ((q.out : P) : Γ)) v) := by
  rw [tSumR_apply]
  have hs := Finset.sum_sigma' X (fun x => (Finset.univ : Finset (RC (Sx P S x))))
    (fun x q => Coinvariants.mk (ρ.comp S.subtype) (ρ (x * ((q.out : P) : Γ)) v))
  refine Eq.trans ?_ hs.symm
  symm
  refine Finset.sum_bij (fun z _ => (Quotient.mk (QuotientGroup.rightRel S) (z.1 * ((z.2.out : P) : Γ)) : RC S))
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · rintro ⟨x, q⟩ hz ⟨x', q'⟩ hz' h
    have hx : x ∈ X := (Finset.mem_sigma.mp hz).1
    have hx' : x' ∈ X := (Finset.mem_sigma.mp hz').1
    have h1 := (rc_eq_iff S _ _).mp h
    have h3 : x = x' := by
      refine hX.disjoint x hx x' hx' ((x' * ((q'.out : P) : Γ)) * (x * ((q.out : P) : Γ))⁻¹) h1 1 S.one_mem
        ((q.out : P) : Γ) (Subtype.property _) ((q'.out : P) : Γ) (Subtype.property _) ?_
      group
    subst h3
    have h4 : (q'.out : P) * (q.out : P)⁻¹ ∈ Sx P S x := by
      rw [mem_Sx]
      have : x * (((q'.out : P) * (q.out : P)⁻¹ : P) : Γ) * x⁻¹ =
          (x * ((q'.out : P) : Γ)) * (x * ((q.out : P) : Γ))⁻¹ := by
        simp [mul_assoc]
      rw [this]
      exact h1
    have h5 : q = q' := by
      have := (rc_eq_iff (Sx P S x) q.out q'.out).mpr h4
      rw [Quotient.out_eq, Quotient.out_eq] at this
      exact this
    subst h5
    rfl
  · intro c _
    obtain ⟨x, hx, s, hs, p, hp, hy⟩ := hX.cover c.out
    refine ⟨⟨x, Quotient.mk _ ⟨p, hp⟩⟩, Finset.mem_sigma.mpr ⟨hx, Finset.mem_univ _⟩, ?_⟩
    set r : P := (Quotient.mk (QuotientGroup.rightRel (Sx P S x)) (⟨p, hp⟩ : P)).out with hr
    have hr1 : (Quotient.mk (QuotientGroup.rightRel (Sx P S x)) r : RC (Sx P S x)) =
        Quotient.mk _ ⟨p, hp⟩ := Quotient.out_eq _
    have hr2 : (⟨p, hp⟩ : P) * r⁻¹ ∈ Sx P S x := (rc_eq_iff _ _ _).mp hr1
    have hr3 : x * ((⟨p, hp⟩ * r⁻¹ : P) : Γ) * x⁻¹ ∈ S := hr2
    have key : (Quotient.mk (QuotientGroup.rightRel S) (x * (r : Γ)) : RC S) =
        Quotient.mk _ c.out := by
      rw [rc_eq_iff]
      have : c.out * (x * (r : Γ))⁻¹ = s * (x * (((⟨p, hp⟩ : P) * r⁻¹ : P) : Γ) * x⁻¹) := by
        rw [hy]
        simp [mul_assoc]
      rw [this]
      exact S.mul_mem hs hr3
    exact key.trans (Quotient.out_eq c)
  · rintro ⟨x, q⟩ _
    refine mk_rep_eq S ρ ?_ v
    exact (Quotient.out_eq _).symm

/-- **Mackey for coinvariants.** -/
theorem tMapR_mackey {X : Finset Γ} (hX : DoubleCosetReps P S X) :
    (tMapR S ρ) ∘ₗ qMap P ρ =
      ∑ x ∈ X, (actMapX P S ρ x) ∘ₗ tMapR (Sx P S x) (ρ.comp P.subtype) := by
  refine Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, qMap_mk, tMapR_mk]
  rw [tSumR_mackey P S ρ hX v]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [tSumR_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [actMapX_mk]
  change _ = Coinvariants.mk (ρ.comp S.subtype) (ρ x (ρ ((q.out : P) : Γ) v))
  rw [map_mul]
  rfl

end Coinv

section Nat

variable {k : Type} [Field k]

/-- The transfer `c_P ⟶ c_{P ∩ x⁻¹ S x}` for the group `P`, as a natural transformation on `Rep Γ`. -/
def tNatPX [S.FiniteIndex] (x : Γ) : cN (k := k) P ⟶ (Rep.resFunctor P.subtype ⋙ cN (Sx P S x)) :=
  Functor.whiskerLeft (Rep.resFunctor P.subtype) (tNatR (Sx P S x))

/-- The action of `x` as a natural transformation. -/
def actNatX (x : Γ) : (Rep.resFunctor P.subtype ⋙ cN (Sx P S x)) ⟶ cN (k := k) S where
  app V := ModuleCat.ofHom (actMapX P S V.ρ x)
  naturality V W f := ModuleCat.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => by
    have h : f.hom (V.ρ x (v : V.V)) = W.ρ x (f.hom (v : V.V)) := Rep.hom_comm_apply f x (v : V.V)
    exact congrArg (Coinvariants.mk (W.ρ.comp S.subtype)) h.symm))

end Nat


section Chain

variable {k : Type} [Field k] [S.FiniteIndex]

theorem hom_sum_f {ι : Type*} {C D : ChainComplex (ModuleCat.{0} k) ℕ} (s : Finset ι) (f : ι → (C ⟶ D)) (i : ℕ) :
    (∑ x ∈ s, f x).f i = ∑ x ∈ s, (f x).f i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih, HomologicalComplex.add_f_apply]

variable (X : Finset Γ)

/-- The chain-level transfer `c_P(Y) → c_{P ∩ x⁻¹ S x}(Res_P Y)`. -/
def TYP (Y : ChainComplex (Rep.{0} k Γ) ℕ) (x : Γ) :
    ((cN P).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y ⟶
      (((Rep.resFunctor P.subtype ⋙ cN (Sx P S x)).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y) :=
  (NatTrans.mapHomologicalComplex (tNatPX P S x) (ComplexShape.down ℕ)).app Y

/-- The chain-level action `c_{P ∩ x⁻¹ S x}(Res_P Y) → c_S(Y)`. -/
def ACTY (Y : ChainComplex (Rep.{0} k Γ) ℕ) (x : Γ) :
    (((Rep.resFunctor P.subtype ⋙ cN (Sx P S x)).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y) ⟶
      ((cN S).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y :=
  (NatTrans.mapHomologicalComplex (actNatX P S x) (ComplexShape.down ℕ)).app Y

/-- **Mackey, chain level.** -/
theorem mackey_chain (hX : DoubleCosetReps P S X) (Y : ChainComplex (Rep.{0} k Γ) ℕ) :
    QY P Y ≫ TYR S Y = ∑ x ∈ X, TYP P S Y x ≫ ACTY P S Y x := by
  refine HomologicalComplex.hom_ext _ _ fun j => ?_
  rw [hom_sum_f]
  simp only [HomologicalComplex.comp_f]
  refine ModuleCat.hom_ext ?_
  rw [ModuleCat.hom_sum]
  simp only [ModuleCat.hom_comp]
  exact tMapR_mackey P S (Y.X j).ρ hX

end Chain


section Conj

open Finsupp MonoidalCategory

variable (A : Rep.{0} ℚ Γ) (x : Γ)

/-- Conjugation by `x`, as a homomorphism `P ∩ x⁻¹ S x → S`. -/
def mX : Sx P S x →* S where
  toFun h := ⟨x * ((h : P) : Γ) * x⁻¹, h.2⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

theorem mX_coe (h : Sx P S x) : ((mX P S x h : S) : Γ) = x * ((h : P) : Γ) * x⁻¹ := rfl

/-- The action of `x`, as a morphism of coefficient modules over `mX`. -/
def aX : Rep.res (Sx P S x).subtype (Rep.res P.subtype A) ⟶
    Rep.res (mX P S x) (Rep.res S.subtype A) :=
  Rep.ofHom ⟨A.ρ x, fun h => by
    ext a
    change A.ρ x (A.ρ (((h : P) : Γ)) a) = A.ρ (x * ((h : P) : Γ) * x⁻¹) (A.ρ x a)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group⟩

/-- The `P`-complex `A₀ ⊗ Res_P bar(Γ)`; it equals `Res_P (A ⊗ bar Γ)` (`Y0_eq`). -/
def Y0 : ChainComplex (Rep.{0} ℚ P) ℕ :=
  ((tensorLeft (Rep.res P.subtype A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (((Rep.resFunctor P.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.barComplex ℚ Γ))

theorem Y0_eq : Y0 P A = ((Rep.resFunctor P.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (YA A) := rfl

/-- The comparison `A₀ ⊗ bar(P) ⟶ A₀ ⊗ Res_P bar(Γ)` of complexes of `P`-modules. -/
def BtP : YA (Rep.res P.subtype A) ⟶ Y0 P A :=
  ((tensorLeft (Rep.res P.subtype A)).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (barMap (k := ℚ) P.subtype)

/-- The chain map `c_{S_x}(A₀ ⊗ bar P) → c_S(A ⊗ bar Γ)` induced by the action of `x`. -/
def PsiX : CxN (Sx P S x) (YA (Rep.res P.subtype A)) ⟶ CxN S (YA A) :=
  ((cN (Sx P S x)).mapHomologicalComplex (ComplexShape.down ℕ)).map (BtP P A) ≫ ACTY P S (YA A) x

theorem chains_conjX :
    groupHomology.chainsMap (mX P S x) (aX P S A x) ≫ betaA S A =
      betaA (Sx P S x) (Rep.res P.subtype A) ≫ PsiX P S A x ≫ FNrt S A x⁻¹ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun y => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, lsingle_apply]
  have eL : ((groupHomology.chainsMap (mX P S x) (aX P S A x)).f n).hom (single y b) =
      single (mX P S x ∘ y) (A.ρ x b) :=
    groupHomology.chainsMap_f_single (mX P S x) (aX P S A x) n y b
  rw [eL, betaA_single S A n (mX P S x ∘ y) (A.ρ x b)]
  have eR := betaA_single (Sx P S x) (Rep.res P.subtype A) n y b
  change _ = ((FNrt S A x⁻¹).f n).hom (((PsiX P S A x).f n).hom
    (((betaA (Sx P S x) (Rep.res P.subtype A)).f n).hom (single y b)))
  rw [eR]
  have hB : ((barTerm (k := ℚ) P.subtype n).hom
      (single (⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : P) (1 : ℚ)))) =
      single (⇑P.subtype ∘ ⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)) := by
    rw [barTerm_single, map_one]
  have hF : (rtTerm (k := ℚ) x⁻¹ n).hom ((Rep.free ℚ Γ (Fin n → Γ)).ρ x
      (single (⇑P.subtype ∘ ⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)))) =
      single (⇑S.subtype ∘ ⇑(mX P S x) ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)) := by
    change (rtTerm (k := ℚ) x⁻¹ n).hom ((Representation.free ℚ Γ (Fin n → Γ)) x
      (single (⇑P.subtype ∘ ⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)))) = _
    rw [Representation.free_single_single, rtTerm_single]
    congr 1
    · funext i
      simp [conjInv_apply, mX_coe, mul_assoc]
    · simp
  change _ = (cN (k := ℚ) S).map ((tensorLeft A).map (rtTerm (k := ℚ) x⁻¹ n))
    (actMapX P S (A ⊗ Rep.free ℚ Γ (Fin n → Γ)).ρ x
      (Coinvariants.mk _ (b ⊗ₜ[ℚ] (barTerm (k := ℚ) P.subtype n).hom
        (single (⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : P) (1 : ℚ))))))
  rw [hB]
  rw [actMapX_mk]
  change _ = Coinvariants.mk _ (A.ρ x b ⊗ₜ[ℚ] (rtTerm (k := ℚ) x⁻¹ n).hom ((Rep.free ℚ Γ (Fin n → Γ)).ρ x
      (single (⇑P.subtype ∘ ⇑(Sx P S x).subtype ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ)))))
  rw [hF]

end Conj


section MackeyH

variable (A : Rep.{0} ℚ Γ)

theorem conj_comparisonX (x : Γ) (n : ℕ) :
    groupHomology.map (mX P S x) (aX P S A x) n ≫ (eN S A n).hom =
      (eN (Sx P S x) (Rep.res P.subtype A) n).hom ≫
        HomologicalComplex.homologyMap (PsiX P S A x) n := by
  have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ n) (chains_conjX P S A x)
  have hA := HomologicalComplex.homologyMap_comp
    (groupHomology.chainsMap (mX P S x) (aX P S A x)) (betaA S A) n
  have hC : HomologicalComplex.homologyMap
      (betaA (Sx P S x) (Rep.res P.subtype A) ≫ PsiX P S A x ≫ FNrt S A x⁻¹) n =
      HomologicalComplex.homologyMap (betaA (Sx P S x) (Rep.res P.subtype A)) n ≫
        HomologicalComplex.homologyMap (PsiX P S A x) n := by
    have c1 := HomologicalComplex.homologyMap_comp (betaA (Sx P S x) (Rep.res P.subtype A))
      (PsiX P S A x ≫ FNrt S A x⁻¹) n
    have c2 := HomologicalComplex.homologyMap_comp (PsiX P S A x) (FNrt S A x⁻¹) n
    have c3 := homologyMap_FNrt S A x⁻¹ n
    refine c1.trans (congrArg (fun z => HomologicalComplex.homologyMap
      (betaA (Sx P S x) (Rep.res P.subtype A)) n ≫ z)
      (c2.trans ((congrArg (fun z => HomologicalComplex.homologyMap (PsiX P S A x) n ≫ z) c3).trans
        (Category.comp_id _))))
  rw [eN_hom, eN_hom]
  exact hA.symm.trans (h1.trans hC)

theorem groupHomologyIso_inst_irrel {G : Type} [Group G] (i j : DecidableEq G) (B : Rep.{0} ℚ G) (m : ℕ)
    (R : CategoryTheory.ProjectiveResolution (Rep.trivial ℚ G ℚ)) :
    @groupHomologyIso ℚ G _ _ i B m R = @groupHomologyIso ℚ G _ _ j B m R := by
  have : i = j := Subsingleton.elim _ _
  subst this
  rfl

theorem eN_eK_BtC (n : ℕ) :
    (eN P A n).hom = (eK (Rep.res P.subtype A) n).hom ≫
      HomologicalComplex.homologyMap
        ((((Rep.coinvariantsTensor ℚ P).obj (Rep.res P.subtype A)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (barMap (k := ℚ) P.subtype)) n := by
  have h := groupHomologyIso_hom_comp (Rep.res P.subtype A) n (P := Rep.barResolution ℚ P)
    (Q := (Rep.resFunctor P.subtype).mapProjectiveResolution (Rep.barResolution ℚ Γ))
    (barMap (k := ℚ) P.subtype) (barMap_pi (k := ℚ) P)
  have hE : eK (Rep.res P.subtype A) n = groupHomologyIso (Rep.res P.subtype A) n (Rep.barResolution ℚ P) :=
    groupHomologyIso_inst_irrel _ _ _ _ _
  rw [hE]
  exact h.symm

theorem BtC_eq :
    (((Rep.coinvariantsTensor ℚ P).obj (Rep.res P.subtype A)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map (barMap (k := ℚ) P.subtype) =
      ((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map (BtP P A) := rfl

theorem TYP_eq [S.FiniteIndex] (Y : ChainComplex (Rep.{0} ℚ Γ) ℕ) (x : Γ) :
    TYP P S Y x = TYR (Sx P S x) (((Rep.resFunctor P.subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj Y) := rfl

theorem eN_eK_BtP (n : ℕ) :
    (eN P A n).hom = (eK (Rep.res P.subtype A) n).hom ≫
      HomologicalComplex.homologyMap
        (((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map (BtP P A)) n :=
  (eN_eK_BtC P A n).trans (congrArg (fun φ => (eK (Rep.res P.subtype A) n).hom ≫
    HomologicalComplex.homologyMap φ n) (BtC_eq P A))

theorem mackey_key [S.FiniteIndex] {X : Finset Γ} (hX : DoubleCosetReps P S X) :
    ((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map (BtP P A) ≫
        (QY P (YA A) ≫ TYR S (YA A)) =
      ∑ x ∈ X, TYR (Sx P S x) (YA (Rep.res P.subtype A)) ≫ PsiX P S A x := by
  have h1 := congrArg (fun z => ((cK (k := ℚ) (K := P)).mapHomologicalComplex (ComplexShape.down ℕ)).map
    (BtP P A) ≫ z) (mackey_chain P S X hX (YA A))
  refine h1.trans ((Preadditive.comp_sum _ _ _).trans (Finset.sum_congr rfl fun x _ => ?_))
  refine (Category.assoc _ _ _).symm.trans ?_
  have hn := (NatTrans.mapHomologicalComplex (tNatR (Sx P S x)) (ComplexShape.down ℕ)).naturality (BtP P A)
  exact (congrArg (fun z => z ≫ ACTY P S (YA A) x) hn).trans (Category.assoc _ _ _)

/-- **Mackey's formula in group homology**: `tr_S^Γ ∘ cor_P^Γ = ∑_x cor ∘ c_x ∘ tr^P_{P ∩ x⁻¹ S x}`. -/
theorem mackeyH [S.FiniteIndex] {X : Finset Γ} (hX : DoubleCosetReps P S X) (n : ℕ) :
    groupHomology.map P.subtype (𝟙 (Rep.res P.subtype A)) n ≫ trR S A n =
      ∑ x ∈ X, trR (Sx P S x) (Rep.res P.subtype A) n ≫ groupHomology.map (mX P S x) (aX P S A x) n := by
  rw [← cancel_mono (eN S A n).hom, Preadditive.sum_comp]
  have L : (groupHomology.map P.subtype (𝟙 (Rep.res P.subtype A)) n ≫ trR S A n) ≫ (eN S A n).hom =
      (eN P A n).hom ≫ HomologicalComplex.homologyMap (QY P (YA A) ≫ TYR S (YA A)) n := by
    unfold trR
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc (groupHomology.map P.subtype _ n), cor_comparison P A n,
      Category.assoc, HomologicalComplex.homologyMap_comp]
  have R : ∀ x ∈ X, (trR (Sx P S x) (Rep.res P.subtype A) n ≫ groupHomology.map (mX P S x) (aX P S A x) n) ≫
      (eN S A n).hom = (eK (Rep.res P.subtype A) n).hom ≫ HomologicalComplex.homologyMap
        (TYR (Sx P S x) (YA (Rep.res P.subtype A)) ≫ PsiX P S A x) n := by
    intro x _
    unfold trR
    simp only [Category.assoc]
    rw [conj_comparisonX P S A x n, ← Category.assoc (eN (Sx P S x) _ n).inv, Iso.inv_hom_id,
      Category.id_comp, HomologicalComplex.homologyMap_comp]
  rw [L, Finset.sum_congr rfl R, ← Preadditive.comp_sum, ← homologyMap_sum']
  rw [eN_eK_BtP P A n]
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun z => (eK (Rep.res P.subtype A) n).hom ≫ z) ?_
  refine (HomologicalComplex.homologyMap_comp _ _ n).symm.trans ?_
  exact congrArg (fun φ => HomologicalComplex.homologyMap φ n) (mackey_key P S A hX)

end MackeyH


section InnerTrivial

open Finsupp MonoidalCategory

variable (A : Rep.{0} ℚ Γ)

/-- Right translation on `CxK`. -/
def FKrt (a : Γ) : CxK (YA A) ⟶ CxK (YA A) :=
  ((cK (k := ℚ) (K := Γ)).mapHomologicalComplex _).map
    (((tensorLeft A).mapHomologicalComplex _).map (rtMap (k := ℚ) a))

theorem homologyMap_FKrt (a : Γ) (n : ℕ) : HomologicalComplex.homologyMap (FKrt A a) n = 𝟙 _ := by
  have h := (cK (k := ℚ) (K := Γ)).mapHomotopy (c := ComplexShape.down ℕ)
    ((tensorLeft A).mapHomotopy (c := ComplexShape.down ℕ) (rtHomotopy (k := ℚ) a))
  have := h.homologyMap_eq n
  simpa [FKrt] using this

theorem chains_inner {H : Type} [Group H] (φ₁ φ₂ : H →* Γ) (γ : Γ) (hφ : ∀ h, φ₁ h = γ * φ₂ h * γ⁻¹)
    (B : Rep.{0} ℚ H) (ψ₁ : B ⟶ Rep.res φ₁ A) (ψ₂ : B ⟶ Rep.res φ₂ A)
    (hψ : ∀ b, ψ₁.hom b = A.ρ γ (ψ₂.hom b)) :
    groupHomology.chainsMap φ₁ ψ₁ ≫ (groupHomology.inhomogeneousChainsIso A).hom =
      groupHomology.chainsMap φ₂ ψ₂ ≫ (groupHomology.inhomogeneousChainsIso A).hom ≫ FKrt A γ⁻¹ := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  refine groupHomology.inhomogeneousChains.ext fun y => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun b => ?_)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    ModuleCat.hom_ofHom, lsingle_apply]
  have e1 : ((groupHomology.chainsMap φ₁ ψ₁).f n).hom (single y b) = single (φ₁ ∘ y) (ψ₁.hom b) :=
    groupHomology.chainsMap_f_single φ₁ ψ₁ n y b
  have e2 : ((groupHomology.chainsMap φ₂ ψ₂).f n).hom (single y b) = single (φ₂ ∘ y) (ψ₂.hom b) :=
    groupHomology.chainsMap_f_single φ₂ ψ₂ n y b
  rw [e1]
  change _ = ((FKrt A γ⁻¹).f n).hom (((groupHomology.inhomogeneousChainsIso A).hom.f n).hom
    (((groupHomology.chainsMap φ₂ ψ₂).f n).hom (single y b)))
  rw [e2, inhomIso_hom_f_single, inhomIso_hom_f_single]
  have hr : (rtTerm (k := ℚ) γ⁻¹ n).hom
      (single (φ₂ ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ))) =
      single (φ₁ ∘ y) (MonoidAlgebra.single γ⁻¹ (1 : ℚ)) := by
    rw [rtTerm_single]
    congr 1
    · funext i
      simp [conjInv_apply, hφ, mul_assoc]
    · simp
  change _ = Coinvariants.mk (A.ρ.tprod (Representation.free ℚ Γ (Fin n → Γ)))
    (ψ₂.hom b ⊗ₜ[ℚ] (rtTerm (k := ℚ) γ⁻¹ n).hom
      (single (φ₂ ∘ y) (MonoidAlgebra.single (1 : Γ) (1 : ℚ))))
  rw [hr, hψ]
  have h := Coinvariants.mk_self_apply (A.ρ.tprod (Representation.free ℚ Γ (Fin n → Γ))) γ
    (ψ₂.hom b ⊗ₜ[ℚ] single (φ₁ ∘ y) (MonoidAlgebra.single γ⁻¹ (1 : ℚ)))
  refine Eq.trans ?_ h
  congr 1
  simp only [Representation.tprod_apply, TensorProduct.map_tmul]
  rw [Representation.free_single_single]
  simp

/-- Inner conjugations act trivially: `H_n(c_γ ∘ φ, ρ(γ) ∘ ψ) = H_n(φ, ψ)` as maps to `H_n(Γ, A)`. -/
theorem map_inner_eq {H : Type} [Group H] (φ₁ φ₂ : H →* Γ) (γ : Γ) (hφ : ∀ h, φ₁ h = γ * φ₂ h * γ⁻¹)
    (B : Rep.{0} ℚ H) (ψ₁ : B ⟶ Rep.res φ₁ A) (ψ₂ : B ⟶ Rep.res φ₂ A)
    (hψ : ∀ b, ψ₁.hom b = A.ρ γ (ψ₂.hom b)) (n : ℕ) :
    groupHomology.map φ₁ ψ₁ n = groupHomology.map φ₂ ψ₂ n := by
  rw [← cancel_mono (eK A n).hom]
  have key : ∀ (f : H →* Γ) (ψ : B ⟶ Rep.res f A), groupHomology.map f ψ n ≫ (eK A n).hom =
      HomologicalComplex.homologyMap (groupHomology.chainsMap f ψ ≫ (groupHomology.inhomogeneousChainsIso A).hom) n := by
    intro f ψ
    rw [groupHomologyIso_bar_hom, HomologicalComplex.homologyMap_comp]
    rfl
  rw [key, key, chains_inner A φ₁ φ₂ γ hφ B ψ₁ ψ₂ hψ]
  have e1 := HomologicalComplex.homologyMap_comp (groupHomology.chainsMap φ₂ ψ₂)
    ((groupHomology.inhomogeneousChainsIso A).hom ≫ FKrt A γ⁻¹) n
  have e2 := HomologicalComplex.homologyMap_comp (groupHomology.inhomogeneousChainsIso A).hom (FKrt A γ⁻¹) n
  have e3 := HomologicalComplex.homologyMap_comp (groupHomology.chainsMap φ₂ ψ₂)
    (groupHomology.inhomogeneousChainsIso A).hom n
  exact e1.trans ((congrArg (fun z => HomologicalComplex.homologyMap (groupHomology.chainsMap φ₂ ψ₂) n ≫ z)
    (e2.trans ((congrArg (fun z => HomologicalComplex.homologyMap
      (groupHomology.inhomogeneousChainsIso A).hom n ≫ z) (homologyMap_FKrt A γ⁻¹ n)).trans
        (Category.comp_id _)))).trans e3.symm)

end InnerTrivial


section HeckeMackey

variable {Ĝ : Type} [Group Ĝ] (ι : Γ →* Ĝ) (hι : Function.Injective ι) {g : Ĝ} (D : HeckeDatum ι g) (M : Rep.{0} ℚ Ĝ)
  (F : Rep.{0} ℚ P) (J : F ⟶ Rep.res P.subtype (Rep.res ι M))

/-- The decomposition of `H_n(J) ≫ heckeOp` along the double cosets, before the `P`-level data is inserted. -/
theorem hecke_decomp [hS : D.S.FiniteIndex] {X : Finset Γ} (hX : DoubleCosetReps P D.S X) (n : ℕ) :
    groupHomology.map P.subtype J n ≫ heckeOp D M n =
      ∑ x ∈ X, groupHomology.map (MonoidHom.id P) J n ≫
        (trR (Sx P D.S x) (Rep.res P.subtype (Rep.res ι M)) n ≫
          groupHomology.map (mX P D.S x) (aX P D.S (Rep.res ι M) x) n) ≫ groupHomology.map D.f (corrMap D M) n := by
  have hmac := mackeyH P D.S (Rep.res ι M) hX n
  have hJ : groupHomology.map P.subtype J n = groupHomology.map (MonoidHom.id P) J n ≫
      groupHomology.map P.subtype (𝟙 (Rep.res P.subtype (Rep.res ι M))) n := by
    have h := groupHomology.map_comp (MonoidHom.id P) P.subtype J
      (𝟙 (Rep.res P.subtype (Rep.res ι M))) n
    exact (groupHomology.map_congr (MonoidHom.comp_id P.subtype).symm rfl n).trans h
  rw [hJ, Category.assoc]
  unfold heckeOp
  rw [← Category.assoc (groupHomology.map P.subtype _ n), hmac, Preadditive.sum_comp, Preadditive.comp_sum]

/-- **The `x`-term of the Hecke operator**: a single double coset contributes the `P`-level correspondence. -/
theorem hecke_mackey_term (hι : Function.Injective ι) [hS : D.S.FiniteIndex] (x : Γ) (γ : Γ) (ξ : Ĝ)
    (hγξ : g * ι x = ι γ * ξ) (fx : Sx P D.S x →* P)
    (hfx : ∀ h : Sx P D.S x, ι ((fx h : P) : Γ) = ξ * ι ((h : P) : Γ) * ξ⁻¹)
    (cx : Rep.res (Sx P D.S x).subtype F ⟶ Rep.res fx F)
    (hcx : ∀ a, J.hom (cx.hom a) = M.ρ ξ (J.hom a)) (n : ℕ) :
    groupHomology.map (MonoidHom.id P) J n ≫
        (trR (Sx P D.S x) (Rep.res P.subtype (Rep.res ι M)) n ≫
          groupHomology.map (mX P D.S x) (aX P D.S (Rep.res ι M) x) n) ≫ groupHomology.map D.f (corrMap D M) n =
      trR (Sx P D.S x) F n ≫ groupHomology.map fx cx n ≫ groupHomology.map P.subtype J n := by
  have hnat := trR_nat (Sx P D.S x) J n
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => z ≫ (groupHomology.map (mX P D.S x) (aX P D.S (Rep.res ι M) x) n ≫
    groupHomology.map D.f (corrMap D M) n)) hnat).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun z => trR (Sx P D.S x) F n ≫ z) ?_
  have e1 := groupHomology.map_comp (mX P D.S x) D.f (aX P D.S (Rep.res ι M) x) (corrMap D M) n
  have e2 := groupHomology.map_comp (C := Rep.res ι M) (MonoidHom.id (Sx P D.S x)) (D.f.comp (mX P D.S x))
    ((Rep.resFunctor (Sx P D.S x).subtype).map J)
    (aX P D.S (Rep.res ι M) x ≫ (Rep.resFunctor (mX P D.S x)).map (corrMap D M)) n
  have e3 := groupHomology.map_comp fx P.subtype cx J n
  rw [← e1, ← e2, ← e3]
  refine map_inner_eq (Rep.res ι M) _ _ γ ?_ _ _ _ ?_ n
  · intro h
    apply hι
    have h1 := D.hf (mX P D.S x h)
    have h3 := hfx h
    change ι ((D.f (mX P D.S x h) : Γ)) = ι (γ * ((fx h : P) : Γ) * γ⁻¹)
    rw [h1, map_mul, map_mul, map_inv, h3, mX_coe]
    simp only [map_mul, map_inv]
    have h4 : g * (ι x * ι ((h : P) : Γ) * (ι x)⁻¹) * g⁻¹ =
        (g * ι x) * ι ((h : P) : Γ) * (g * ι x)⁻¹ := by group
    rw [h4, hγξ]
    group
  · intro b
    change M.ρ g (M.ρ (ι x) (J.hom b)) = M.ρ (ι γ) (J.hom (cx.hom b))
    rw [hcx b, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hγξ]

/-- **Hecke operators and Shapiro (Mackey), two double cosets.**  If `S\Γ/P` has the two representatives `x₀ ≠ x₁`
and, for `i = 0, 1`, `g xᵢ = γᵢ ξᵢ` with `ξᵢ` conjugating `P ∩ xᵢ⁻¹ S xᵢ` into `P` compatibly with the fibre
inclusion `J`, then the Hecke operator on `H_n(Γ, M)` restricted to the image of `H_n(P, F)` is the sum of the two
`P`-level correspondences. -/
theorem hecke_mackey_pair [DecidableEq Γ] (hι : Function.Injective ι) [hS : D.S.FiniteIndex] {x₀ x₁ : Γ} (hne : x₀ ≠ x₁)
    (hX : DoubleCosetReps P D.S {x₀, x₁})
    (γ₀ γ₁ : Γ) (ξ₀ ξ₁ : Ĝ) (hγξ₀ : g * ι x₀ = ι γ₀ * ξ₀) (hγξ₁ : g * ι x₁ = ι γ₁ * ξ₁)
    (f₀ : Sx P D.S x₀ →* P) (f₁ : Sx P D.S x₁ →* P)
    (hf₀ : ∀ h : Sx P D.S x₀, ι ((f₀ h : P) : Γ) = ξ₀ * ι ((h : P) : Γ) * ξ₀⁻¹)
    (hf₁ : ∀ h : Sx P D.S x₁, ι ((f₁ h : P) : Γ) = ξ₁ * ι ((h : P) : Γ) * ξ₁⁻¹)
    (c₀ : Rep.res (Sx P D.S x₀).subtype F ⟶ Rep.res f₀ F)
    (c₁ : Rep.res (Sx P D.S x₁).subtype F ⟶ Rep.res f₁ F)
    (hc₀ : ∀ a, J.hom (c₀.hom a) = M.ρ ξ₀ (J.hom a)) (hc₁ : ∀ a, J.hom (c₁.hom a) = M.ρ ξ₁ (J.hom a)) (n : ℕ) :
    groupHomology.map P.subtype J n ≫ heckeOp D M n =
      (trR (Sx P D.S x₀) F n ≫ groupHomology.map f₀ c₀ n ≫ groupHomology.map P.subtype J n) +
      (trR (Sx P D.S x₁) F n ≫ groupHomology.map f₁ c₁ n ≫ groupHomology.map P.subtype J n) := by
  rw [hecke_decomp P ι D M F J hX n, Finset.sum_pair hne,
    hecke_mackey_term P ι D M F J hι x₀ γ₀ ξ₀ hγξ₀ f₀ hf₀ c₀ hc₀ n,
    hecke_mackey_term P ι D M F J hι x₁ γ₁ ξ₁ hγξ₁ f₁ hf₁ c₁ hc₁ n]

end HeckeMackey

end TernaryPeriodPolynomials.Argument.HeckeHomology
