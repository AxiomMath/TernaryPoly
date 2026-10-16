module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.Setup
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.CorrResolution
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ProjRes

@[expose] public section


/-!
# The quotient correspondence `ζ : Res_{Γ₀} Z ⟶ Res_χ Z` attached to a correspondence on `P` modulo a normal subgroup `U`

Formalized by Claude Sonnet 5.5.

For `U ⊲ P`, a finite-index subgroup `S ≤ P`, a homomorphism `f : S →* P` with `f(S ∩ U) ⊆ U`, a coefficient morphism
`c : Res_S A ⟶ Res_f A` and a lift `lam` of `(S, f)` to the bar resolution of `P` (a chain map `Res_S bar ⟶ Res_f bar` over the
identity), we build

* `G0 U S ≤ P/U` (the image of `S`) and `chi : G0 U S →* P/U` (induced by `f`);
* the radical operator `zU`: the transfer `U ⊃ S ∩ U` followed by `(c, lam)`, computed in the `U`-coinvariant complex of
  `A ⊗ bar(P)` by the resolution-model operator `ResCorr` of the group `U` (`zetaLin_mk`: `[a ⊗ r] ↦ ∑_{(S∩U)u} [c(ua) ⊗ lam(ur)]`);
* `zetaC : Res_{Γ₀} (ZP U A) ⟶ Res_χ (ZP U A)`, a chain map of `Γ₀`-representations (`zetaLin_equivariant`: the equivariance
  uses that conjugation by `s ∈ S` permutes `(S ∩ U)\U`, `sum_rc_equiv`).
-/

open CategoryTheory MonoidalCategory Representation Representation.Coinvariants
open TernaryPeriodPolynomials.Argument.HochschildSerre TernaryPeriodPolynomials.Argument.GroupHomology

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

section Quot

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P)

/-- The image `Γ₀` of `S` in `P/U`. -/
def G0 : Subgroup (P ⧸ U) := S.map (QuotientGroup.mk' U)

theorem mem_G0 (q : P ⧸ U) : q ∈ G0 U S ↔ ∃ s ∈ S, QuotientGroup.mk s = q := by
  simp [G0, Subgroup.mem_map]

instance [S.FiniteIndex] : (G0 U S).FiniteIndex := by
  refine ⟨fun h => ?_⟩
  have h1 : (S.map (QuotientGroup.mk' U)).index ∣ S.index :=
    Subgroup.index_map_dvd S (QuotientGroup.mk'_surjective U)
  have h2 : S.index = 0 := Nat.eq_zero_of_zero_dvd (h ▸ h1)
  exact Subgroup.FiniteIndex.index_ne_zero (H := S) h2

/-- The surjection `S → Γ₀`. -/
def piS : S →* G0 U S := (QuotientGroup.mk' U).subgroupMap S

theorem piS_surjective : Function.Surjective (piS U S) :=
  MonoidHom.subgroupMap_surjective _ _

theorem piS_coe (s : S) : ((piS U S s : G0 U S) : P ⧸ U) = QuotientGroup.mk (s : P) := rfl

variable (f : S →* P) (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U)

/-- The homomorphism `χ : Γ₀ → P/U` induced by `f`. -/
def chi : G0 U S →* P ⧸ U :=
  (piS U S).liftOfRightInverse (Function.surjInv (piS_surjective U S))
    (Function.rightInverse_surjInv (piS_surjective U S))
    ⟨(QuotientGroup.mk' U).comp f, by
      intro s hs
      rw [MonoidHom.mem_ker] at hs ⊢
      have h1 : ((piS U S s : G0 U S) : P ⧸ U) = 1 := by rw [hs]; rfl
      rw [piS_coe, QuotientGroup.eq_one_iff] at h1
      show QuotientGroup.mk (f s) = 1
      rw [QuotientGroup.eq_one_iff]
      exact hfU s h1⟩

theorem chi_piS (s : S) : chi U S f hfU (piS U S s) = QuotientGroup.mk (f s) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ s

end Quot

section UData

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex] (f : S →* P)
  (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U)

/-- `S ∩ U` as a subgroup of `U`. -/
abbrev U1 : Subgroup U := S.subgroupOf U

/-- The inclusion `S ∩ U → S`. -/
def incl1 : U1 U S →* S := MonoidHom.codRestrict (U.subtype.comp (U1 U S).subtype) S (fun u => u.2)

/-- The restriction of `f` to `S ∩ U`, landing in `U`. -/
def nuU : U1 U S →* U :=
  MonoidHom.codRestrict (f.comp (incl1 U S)) U (fun u => hfU (incl1 U S u) u.1.2)

variable (A : Rep.{0} ℚ P) (c : Rep.res S.subtype A ⟶ Rep.res f A)

/-- The coefficient morphism of the radical correspondence. -/
def cU : Rep.res (U1 U S).subtype (Rep.res U.subtype A) ⟶ Rep.res (nuU U S f hfU) (Rep.res U.subtype A) :=
  (Rep.resFunctor (incl1 U S)).map c

/-- The restriction to `U` of the bar resolution of `P`. -/
abbrev RU : ProjectiveResolution (Rep.trivial ℚ U ℚ) :=
  (Rep.resFunctor U.subtype).mapProjectiveResolution (Rep.barResolution ℚ P)

variable (lam : LiftG (Rep.barResolution ℚ P) S f)

/-- The restriction of the lift to `S ∩ U`. -/
def lamU : LiftG (RU U) (U1 U S) (nuU U S f hfU) :=
  ((Rep.resFunctor (incl1 U S)).mapHomologicalComplex (ComplexShape.down ℕ)).map lam

/-- **The radical part of the correspondence** on the `U`-coinvariant complex of `A ⊗ bar(P)`:
`[a ⊗ r] ↦ ∑_{U₁ u ∈ U₁\U} [c (u a) ⊗ lam (u r)]`. -/
def zU : (RU U).complex.coinvariantsTensorObj (Rep.res U.subtype A) ⟶
    (RU U).complex.coinvariantsTensorObj (Rep.res U.subtype A) :=
  ResCorr (Rep.res U.subtype A) (RU U) (U1 U S) (nuU U S f hfU) (cU U S f hfU A c) (lamU U S f hfU lam)

end UData

section Conj

open scoped Classical

variable {K : Type} [Group K] (N : Subgroup K) [N.FiniteIndex] (e : K ≃* K) (he : ∀ k, e k ∈ N ↔ k ∈ N)

include he

/-- A multiplicative automorphism preserving `N` acts on the right cosets `N\K`. -/
def rcEquiv : RC N ≃ RC N where
  toFun := Quotient.map' e (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    have : e b * (e a)⁻¹ = e (b * a⁻¹) := by simp
    rw [this]
    exact (he _).2 hab)
  invFun := Quotient.map' e.symm (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    have : e.symm b * (e.symm a)⁻¹ = e.symm (b * a⁻¹) := by simp
    rw [this]
    have h2 := (he (e.symm (b * a⁻¹))).1
    simp only [MulEquiv.apply_symm_apply] at h2
    exact h2 hab)
  left_inv x := by
    induction x using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']
  right_inv x := by
    induction x using Quotient.inductionOn' with
    | h a => simp [Quotient.map'_mk'']

omit [N.FiniteIndex] in
theorem rcEquiv_mk (a : K) : rcEquiv N e he (Quotient.mk _ a) = Quotient.mk _ (e a) := rfl

/-- Sums over `N\K` of a left-`N`-invariant function can be reindexed along `e`. -/
theorem sum_rc_equiv {M : Type*} [AddCommMonoid M] (g : K → M) (hg : ∀ n : N, ∀ k, g (n * k) = g k) :
    ∑ x : RC N, g (e x.out) = ∑ x : RC N, g x.out := by
  have key : ∀ x : RC N, g (e x.out) = g ((rcEquiv N e he x).out) := by
    intro x
    have h1 : rcEquiv N e he x = Quotient.mk _ (e x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    have h2 : (Quotient.mk (QuotientGroup.rightRel N) (e x.out) : RC N) =
        Quotient.mk _ ((rcEquiv N e he x).out) := by
      rw [← h1]; exact (Quotient.out_eq _).symm
    rw [rc_eq_iff] at h2
    have h3 : (rcEquiv N e he x).out = ((rcEquiv N e he x).out * (e x.out)⁻¹) * e x.out := by group
    rw [h3, hg ⟨_, h2⟩]
  simp only [key]
  exact Equiv.sum_comp (rcEquiv N e he) (fun y : RC N => g y.out)

end Conj

section ZetaRep

open scoped Classical

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal] (S : Subgroup P) [S.FiniteIndex] (f : S →* P)
  (hfU : ∀ s : S, (s : P) ∈ U → f s ∈ U) (A : Rep.{0} ℚ P) (c : Rep.res S.subtype A ⟶ Rep.res f A)
  (lam : LiftG (Rep.barResolution ℚ P) S f)

/-- The underlying linear map of the coefficient morphism `c`. -/
def cLin : A.V →ₗ[ℚ] A.V := c.hom.toLinearMap

omit [U.Normal] [S.FiniteIndex] in
theorem cLin_equiv (s : S) (a : A.V) : cLin S f A c (A.ρ (s : P) a) = A.ρ (f s) (cLin S f A c a) :=
  Rep.hom_comm_apply c s a

/-- The underlying linear map of the lift in degree `j`. -/
def lamLin (j : ℕ) : ((Rep.barComplex ℚ P).X j).V →ₗ[ℚ] ((Rep.barComplex ℚ P).X j).V :=
  (lam.f j).hom.toLinearMap

omit [U.Normal] [S.FiniteIndex] in
theorem lamLin_equiv (j : ℕ) (s : S) (r : ((Rep.barComplex ℚ P).X j).V) :
    lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (s : P) r) =
      ((Rep.barComplex ℚ P).X j).ρ (f s) (lamLin S f lam j r) :=
  Rep.hom_comm_apply (lam.f j) s r

/-- The underlying linear map of the radical operator in degree `j`. -/
def zetaLin (j : ℕ) : ((ZP U A).X j).V →ₗ[ℚ] ((ZP U A).X j).V :=
  ((zU U S f hfU A c lam).f j).hom

/-- The radical operator on generators. -/
theorem zetaLin_mk (j : ℕ) (a : A) (r : (Rep.barComplex ℚ P).X j) :
    zetaLin U S f hfU A c lam j
        (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r)) =
      ∑ x : RC (U1 U S), Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ (x.out : U) a) ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r)) :=
  ResCorr_f_mk (Rep.res U.subtype A) (RU U) (U1 U S) (nuU U S f hfU) (cU U S f hfU A c)
    (lamU U S f hfU lam) j a r

omit [U.Normal] [S.FiniteIndex] in
include hfU in
/-- The class `g(u)` is constant on cosets `U₁ u`. -/
theorem zeta_g_invariant (j : ℕ) (a' : A) (r' : (Rep.barComplex ℚ P).X j) (n : U1 U S) (u : U) :
    Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ ((n * u : U) : P) a') ⊗ₜ[ℚ]
          lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ ((n * u : U) : P) r')) =
      Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ (u : P) a') ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (u : P) r')) := by
  have hn : ((n : U) : P) = ((incl1 U S n : S) : P) := rfl
  have e1 : A.ρ ((n * u : U) : P) a' = A.ρ ((incl1 U S n : S) : P) (A.ρ (u : P) a') := by
    rw [show ((n * u : U) : P) = ((incl1 U S n : S) : P) * (u : P) from rfl, map_mul]
    rfl
  have e2 : ((Rep.barComplex ℚ P).X j).ρ ((n * u : U) : P) r' =
      ((Rep.barComplex ℚ P).X j).ρ ((incl1 U S n : S) : P)
        (((Rep.barComplex ℚ P).X j).ρ (u : P) r') := by
    rw [show ((n * u : U) : P) = ((incl1 U S n : S) : P) * (u : P) from rfl, map_mul]
    rfl
  have h1 : cLin S f A c (A.ρ ((n * u : U) : P) a') = A.ρ (f (incl1 U S n)) (cLin S f A c (A.ρ (u : P) a')) := by
    rw [e1]
    exact Rep.hom_comm_apply c (incl1 U S n) (A.ρ (u : P) a')
  have h2 : lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ ((n * u : U) : P) r') =
      ((Rep.barComplex ℚ P).X j).ρ (f (incl1 U S n))
        (lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (u : P) r')) := by
    rw [e2]
    exact Rep.hom_comm_apply (lam.f j) (incl1 U S n) (((Rep.barComplex ℚ P).X j).ρ (u : P) r')
  rw [h1, h2]
  exact Coinvariants.mk_self_apply (((YA A).X j).ρ.comp U.subtype) ⟨f (incl1 U S n), hfU _ n.1.2⟩
    (cLin S f A c (A.ρ (u : P) a') ⊗ₜ[ℚ] lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (u : P) r'))


theorem rho_conj_apply {V : Type*} [AddCommGroup V] [Module ℚ V] (ρ : Representation ℚ P V) (s x : P) (v : V) :
    ρ (s * x * s⁻¹) (ρ s v) = ρ s (ρ x v) := by
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem zetaLin_equivariant (s : S) (j : ℕ) :
    zetaLin U S f hfU A c lam j ∘ₗ ((ZP U A).X j).ρ (QuotientGroup.mk (s : P)) =
      ((ZP U A).X j).ρ (QuotientGroup.mk (f s)) ∘ₗ zetaLin U S f hfU A c lam j := by
  refine Coinvariants.hom_ext (TensorProduct.ext' fun a (r : (Rep.barComplex ℚ P).X j) => ?_)
  show zetaLin U S f hfU A c lam j (((ZP U A).X j).ρ (QuotientGroup.mk (s : P))
      (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r))) =
    ((ZP U A).X j).ρ (QuotientGroup.mk (f s)) (zetaLin U S f hfU A c lam j
      (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r)))
  have e1 : ((ZP U A).X j).ρ (QuotientGroup.mk (s : P))
      (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype) (a ⊗ₜ[ℚ] r)) =
      Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (A.ρ (s : P) a ⊗ₜ[ℚ] ((Rep.barComplex ℚ P).X j).ρ (s : P) r) := rfl
  refine (congrArg (zetaLin U S f hfU A c lam j) e1).trans ?_
  set g : U → Coinvariants (((YA A).X j).ρ.comp U.subtype) := fun u =>
    Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (cLin S f A c (A.ρ (u : P) (A.ρ (s : P) a)) ⊗ₜ[ℚ]
        lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (u : P)
          (((Rep.barComplex ℚ P).X j).ρ (s : P) r))) with hg
  have hL : ∑ x : RC (U1 U S), Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (cLin S f A c (A.ρ (x.out : U) (A.ρ (s : P) a)) ⊗ₜ[ℚ]
        lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (x.out : U)
          (((Rep.barComplex ℚ P).X j).ρ (s : P) r))) = ∑ x : RC (U1 U S), g x.out := rfl
  have hR : ∀ x : RC (U1 U S),
      ((ZP U A).X j).ρ (QuotientGroup.mk (f s)) (Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ (x.out : U) a) ⊗ₜ[ℚ]
          lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r))) =
      g (MulAut.conjNormal (s : P) x.out) := by
    intro x
    have hc := cLin_equiv S f A c s (A.ρ (x.out : U) a)
    have hl := lamLin_equiv S f lam j s (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r)
    have ec : A.ρ ((MulAut.conjNormal (s : P) x.out : U) : P) (A.ρ (s : P) a) = A.ρ (s : P) (A.ρ (x.out : U) a) := by
      rw [MulAut.conjNormal_apply]
      exact rho_conj_apply A.ρ (s : P) (x.out : U) a
    have el : ((Rep.barComplex ℚ P).X j).ρ ((MulAut.conjNormal (s : P) x.out : U) : P)
        (((Rep.barComplex ℚ P).X j).ρ (s : P) r) =
        ((Rep.barComplex ℚ P).X j).ρ (s : P)
          (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r) := by
      rw [MulAut.conjNormal_apply]
      exact rho_conj_apply ((Rep.barComplex ℚ P).X j).ρ (s : P) (x.out : U) r
    change Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (A.ρ (f s) (cLin S f A c (A.ρ (x.out : U) a)) ⊗ₜ[ℚ]
        ((Rep.barComplex ℚ P).X j).ρ (f s) (lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r))) = _
    rw [hg]
    dsimp only
    rw [ec, el]
    change Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
      (A.ρ (f s) (cLin S f A c (A.ρ (x.out : U) a)) ⊗ₜ[ℚ]
        ((Rep.barComplex ℚ P).X j).ρ (f s) (lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r))) =
      Coinvariants.mk (((YA A).X j).ρ.comp U.subtype)
        (cLin S f A c (A.ρ (s : P) (A.ρ (x.out : U) a)) ⊗ₜ[ℚ]
          lamLin S f lam j (((Rep.barComplex ℚ P).X j).ρ (s : P) (((Rep.barComplex ℚ P).X j).ρ (x.out : U) r)))
    rw [← hc, ← hl]
  have he : ∀ k : U, (MulAut.conjNormal (s : P) k) ∈ U1 U S ↔ k ∈ U1 U S := by
    intro k
    change (((MulAut.conjNormal (s : P) k : U)) : P) ∈ S ↔ (k : P) ∈ S
    rw [MulAut.conjNormal_apply]
    show (s : P) * k * (s : P)⁻¹ ∈ S ↔ (k : P) ∈ S
    constructor
    · intro h
      have := S.mul_mem (S.mul_mem (S.inv_mem s.2) h) s.2
      simpa [mul_assoc] using this
    · intro h
      exact S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2)
  have hsum := sum_rc_equiv (U1 U S) (MulAut.conjNormal (s : P)) he g (fun n k =>
    zeta_g_invariant U S f hfU A c lam j (A.ρ (s : P) a)
      (((Rep.barComplex ℚ P).X j).ρ (s : P) r) n k)
  have step1 := zetaLin_mk U S f hfU A c lam j (A.ρ (s : P) a) (((Rep.barComplex ℚ P).X j).ρ (s : P) r)
  have step2 := congrArg (((ZP U A).X j).ρ (QuotientGroup.mk (f s))) (zetaLin_mk U S f hfU A c lam j a r)
  refine step1.trans (hL.trans (hsum.symm.trans ?_))
  refine Eq.trans ?_ step2.symm
  refine Eq.trans ?_ (map_sum _ _ _).symm
  exact Finset.sum_congr rfl fun x _ => (hR x).symm


/-- **The quotient chain map** `ζ : Res_{Γ₀} Z ⟶ Res_χ Z` of `P/U`-representations in degree `j`. -/
def zetaRep (j : ℕ) :
    Rep.res (G0 U S).subtype ((ZP U A).X j) ⟶ Rep.res (chi U S f hfU) ((ZP U A).X j) :=
  Rep.ofHom ⟨zetaLin U S f hfU A c lam j, fun γ => by
    obtain ⟨s, rfl⟩ := piS_surjective U S γ
    have h := zetaLin_equivariant U S f hfU A c lam s j
    have e : chi U S f hfU (piS U S s) = QuotientGroup.mk (f s) := chi_piS U S f hfU s
    change zetaLin U S f hfU A c lam j ∘ₗ ((ZP U A).X j).ρ (((piS U S s : G0 U S)) : P ⧸ U) =
      ((ZP U A).X j).ρ (chi U S f hfU (piS U S s)) ∘ₗ zetaLin U S f hfU A c lam j
    rw [e]
    exact h⟩

theorem zetaRep_hom (j : ℕ) (w : ((ZP U A).X j).V) :
    (zetaRep U S f hfU A c lam j).hom w = zetaLin U S f hfU A c lam j w := rfl

/-- **The chain map `ζ`.** -/
def zetaC : ((Rep.resFunctor (G0 U S).subtype).mapHomologicalComplex (ComplexShape.down ℕ)).obj (ZP U A) ⟶
    ((Rep.resFunctor (chi U S f hfU)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (ZP U A) where
  f j := zetaRep U S f hfU A c lam j
  comm' := by
    rintro i j (rfl : j + 1 = i)
    refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_))
    have h := congrArg (fun m => m.hom w) ((zU U S f hfU A c lam).comm (j + 1) j)
    exact h

end ZetaRep
