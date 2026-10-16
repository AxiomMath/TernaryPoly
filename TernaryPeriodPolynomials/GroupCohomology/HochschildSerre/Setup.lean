module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.QSide
public import TernaryPeriodPolynomials.GroupCohomology.Homology.NormalDescent
public import TernaryPeriodPolynomials.GroupCohomology.Koszul.ResComp

@[expose] public section


/-!
# The Hochschild-Serre set-up: `P/U`-complex of `U`-coinvariants of `A ⊗ bar(P)`

Formalized by Claude Sonnet 5.5.

For a normal subgroup `U ⊲ P` and `A : Rep ℚ P`, `ZP U A` is the complex of `P/U`-representations obtained by taking
`U`-coinvariants (with their residual `P/U`-action, Mathlib's `Rep.quotientToCoinvariantsFunctor`) of the projective
resolution `A ⊗ bar(P) → A`.

* `Phi_projective`, `ZP_projective`: `Φ` preserves projectives, so `ZP U A` is a complex of projective `P/U`-modules;
* `ZIso`, `groupHomologyZIso`: `(ZP U A ⊗ 1)_{P/U}` is the complex of `P`-coinvariants of `A ⊗ bar(P)`, so its homology is
  `H_n(P, A)` (iterated coinvariants `coinvIterIso`);
* `isZero_ZP_homology`: `H_n(ZP U A) ≅ H_n(U, A)` as vector spaces, hence vanishes when `H_n(U, A)` does.

The underlying vector space of `H_n(ZP U A)` is `H_n(U, A)` and `P/U` acts by the conjugation action (`eN`).
-/

open CategoryTheory MonoidalCategory Representation Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HochschildSerre

variable {P : Type} [Group P] (U : Subgroup P) [U.Normal]

/-- Inflation along `P → P/U`. -/
abbrev infl : Rep.{0} ℚ (P ⧸ U) ⥤ Rep.{0} ℚ P := Rep.resFunctor (QuotientGroup.mk' U)

/-- `X ↦ X_U` as a `P/U`-representation. -/
abbrev Phi : Rep.{0} ℚ P ⥤ Rep.{0} ℚ (P ⧸ U) := Rep.quotientToCoinvariantsFunctor ℚ U

instance : (Phi U).Additive where
  map_add {X Y f g} := by
    ext x
    have h : (Rep.resFunctor U.subtype).map (f + g) =
        (Rep.resFunctor U.subtype).map f + (Rep.resFunctor U.subtype).map g :=
      CategoryTheory.Functor.map_add _
    change ((Rep.coinvariantsFunctor ℚ U).map ((Rep.resFunctor U.subtype).map (f + g))).hom x =
      ((Rep.coinvariantsFunctor ℚ U).map ((Rep.resFunctor U.subtype).map f)).hom x +
        ((Rep.coinvariantsFunctor ℚ U).map ((Rep.resFunctor U.subtype).map g)).hom x
    rw [h, CategoryTheory.Functor.map_add]
    rfl

/-- The quotient map `X → X_U`, a `P`-map to the inflation of `Φ X`. -/
def unitPhi (X : Rep.{0} ℚ P) : X ⟶ (infl U).obj ((Phi U).obj X) := Rep.toCoinvariantsMkQ X U

theorem unitPhi_apply (X : Rep.{0} ℚ P) (x : X) :
    (unitPhi U X).hom x = Coinvariants.mk (X.ρ.comp U.subtype) x := rfl

theorem Phi_projective (X : Rep.{0} ℚ P) [Projective X] : Projective ((Phi U).obj X) where
  factors {E M} f e he := by
    classical
    have hepi : Epi ((infl U).map e) := by
      rw [Rep.epi_iff_surjective] at he ⊢
      exact he
    obtain ⟨g, hg⟩ := Projective.factors (unitPhi U X ≫ (infl U).map f) ((infl U).map e)
    have hgU : ∀ u : U, ∀ x : X, g.hom (X.ρ u x) = g.hom x := by
      intro u x
      have h1 : g.hom (X.ρ u x) = ((infl U).obj E).ρ u (g.hom x) := (Rep.hom_comm_apply g u x)
      rw [h1]
      change E.ρ (QuotientGroup.mk' U u) (g.hom x) = _
      have : QuotientGroup.mk' U u = 1 := (QuotientGroup.eq_one_iff u.1).2 u.2
      rw [this, map_one]
      rfl
    let g' : (Phi U).obj X →ₗ[ℚ] E :=
      Coinvariants.lift (X.ρ.comp U.subtype) g.hom.toLinearMap (fun u => LinearMap.ext fun x => hgU u x)
    have hgx : ∀ x : X, e.hom (g.hom x) = f.hom (Coinvariants.mk (X.ρ.comp U.subtype) x) := fun x =>
      congrArg (fun φ => φ.hom x) hg
    refine ⟨Rep.ofHom ⟨g', fun q => ?_⟩, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H p =>
        refine LinearMap.ext fun z => ?_
        induction z using Coinvariants.induction_on with
        | h x =>
          change g.hom (X.ρ p x) = E.ρ (QuotientGroup.mk' U p) (g.hom x)
          exact Rep.hom_comm_apply g p x
    · refine Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun z => ?_))
      induction z using Coinvariants.induction_on with
      | h x => exact hgx x

open TernaryPeriodPolynomials.Argument.GroupHomology

/-- The complex of `U`-coinvariants of `A ⊗ bar(P)`, with its `P/U`-action. -/
abbrev ZP (A : Rep.{0} ℚ P) : ChainComplex (Rep.{0} ℚ (P ⧸ U)) ℕ :=
  ((Phi U).mapHomologicalComplex (ComplexShape.down ℕ)).obj (YA A)

theorem ZP_projective (A : Rep.{0} ℚ P) (j : ℕ) : Projective ((ZP U A).X j) := by
  have h1 : Projective ((YA A).X j) :=
    (tensorLeft A).projective_obj_of_projective ((Rep.barResolution ℚ P).projective j)
  exact Phi_projective U _

/-- `(X_U)_{P/U} → X_P`. -/
def coinvIterTo (X : Rep.{0} ℚ P) : Coinvariants ((Phi U).obj X).ρ →ₗ[ℚ] Coinvariants X.ρ :=
  Coinvariants.lift ((Phi U).obj X).ρ
    (Coinvariants.lift (X.ρ.comp U.subtype) (Coinvariants.mk X.ρ) (fun u => LinearMap.ext fun v =>
      Coinvariants.mk_self_apply X.ρ u.1 v))
    (fun q => by
      induction q using QuotientGroup.induction_on with
      | H p =>
        refine Coinvariants.hom_ext (LinearMap.ext fun v => ?_)
        exact Coinvariants.mk_self_apply X.ρ p v)

/-- `X_P → (X_U)_{P/U}`. -/
def coinvIterFrom (X : Rep.{0} ℚ P) : Coinvariants X.ρ →ₗ[ℚ] Coinvariants ((Phi U).obj X).ρ :=
  Coinvariants.lift X.ρ
    ((Coinvariants.mk ((Phi U).obj X).ρ).comp (Coinvariants.mk (X.ρ.comp U.subtype)))
    (fun p => LinearMap.ext fun v =>
      Coinvariants.mk_self_apply ((Phi U).obj X).ρ (QuotientGroup.mk p)
        (Coinvariants.mk (X.ρ.comp U.subtype) v))

theorem coinvIterTo_mk (X : Rep.{0} ℚ P) (v : X) :
    coinvIterTo U X (Coinvariants.mk ((Phi U).obj X).ρ (Coinvariants.mk (X.ρ.comp U.subtype) v)) =
      Coinvariants.mk X.ρ v := rfl

theorem coinvIterFrom_mk (X : Rep.{0} ℚ P) (v : X) :
    coinvIterFrom U X (Coinvariants.mk X.ρ v) =
      Coinvariants.mk ((Phi U).obj X).ρ (Coinvariants.mk (X.ρ.comp U.subtype) v) := rfl

/-- Coinvariants of the coinvariants. -/
def coinvIterEquiv (X : Rep.{0} ℚ P) :
    Coinvariants ((Phi U).obj X).ρ ≃ₗ[ℚ] Coinvariants X.ρ :=
  LinearEquiv.ofLinearMap (coinvIterTo U X) (coinvIterFrom U X)
    (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl))
    (Coinvariants.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun _ => rfl)))

/-- `(Φ X)_{P/U} ≅ X_P`, naturally. -/
def coinvIterIso : Phi U ⋙ Rep.coinvariantsFunctor ℚ (P ⧸ U) ≅ Rep.coinvariantsFunctor ℚ P :=
  NatIso.ofComponents (fun X => (coinvIterEquiv U X).toModuleIso) (fun {X Y} f => by
    refine ModuleCat.hom_ext (Coinvariants.hom_ext (Coinvariants.hom_ext (LinearMap.ext fun v => ?_)))
    rfl)

/-- `(N ⊗ 1)_Q ≅ N_Q`, naturally. -/
def FXunitIso {Q : Type} [Group Q] : FX (𝟙_ (Rep.{0} ℚ Q)) ≅ Rep.coinvariantsFunctor ℚ Q :=
  NatIso.ofComponents (fun N => (Rep.coinvariantsFunctor ℚ Q).mapIso (ρ_ N)) (fun {N N'} f => by
    change (Rep.coinvariantsFunctor ℚ Q).map (f ▷ 𝟙_ (Rep.{0} ℚ Q)) ≫
        (Rep.coinvariantsFunctor ℚ Q).map (ρ_ N').hom =
      (Rep.coinvariantsFunctor ℚ Q).map (ρ_ N).hom ≫ (Rep.coinvariantsFunctor ℚ Q).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      MonoidalCategory.rightUnitor_naturality])

/-- The natural isomorphism `(Φ X ⊗ 1)_{P/U} ≅ X_P`. -/
def coinvIso : Phi U ⋙ FX (𝟙_ (Rep.{0} ℚ (P ⧸ U))) ≅ Rep.coinvariantsFunctor ℚ P :=
  Functor.isoWhiskerLeft (Phi U) FXunitIso ≪≫ coinvIterIso U

/-- The complex `(Z ⊗ 1)_{P/U}` is the complex of `P`-coinvariants of `A ⊗ bar(P)`. -/
def ZIso (A : Rep.{0} ℚ P) : CxF (ZP U A) (𝟙_ (Rep.{0} ℚ (P ⧸ U))) ≅ CxK (YA A) :=
  HomologicalComplex.Hom.isoOfComponents (fun j => (coinvIso U).app ((YA A).X j))
    (fun i j _ => ((coinvIso U).hom.naturality ((YA A).d i j)).symm)

/-- `H_n(P, A) ≅ H_n((Z ⊗ 1)_{P/U})`. -/
def groupHomologyZIso (A : Rep.{0} ℚ P) (n : ℕ) :
    groupHomology A n ≅ (CxF (ZP U A) (𝟙_ (Rep.{0} ℚ (P ⧸ U)))).homology n :=
  eK A n ≪≫ (HomologicalComplex.homologyMapIso (ZIso U A) n).symm

theorem isZero_ZP_homology (A : Rep.{0} ℚ P) (n : ℕ)
    (h : IsZero (groupHomology (Rep.res U.subtype A) n)) : IsZero ((ZP U A).homology n) := by
  let F := forget₂ (Rep.{0} ℚ (P ⧸ U)) (ModuleCat ℚ)
  have h1 : IsZero ((CxN U (YA A)).homology n) := IsZero.of_iso h (eN U A n).symm
  have h2 : IsZero (F.obj ((ZP U A).homology n)) :=
    IsZero.of_iso h1 (((ZP U A).sc n).mapHomologyIso F).symm
  rw [Rep.isZero_iff]
  exact (ModuleCat.isZero_iff_subsingleton).1 h2

end TernaryPeriodPolynomials.Argument.HochschildSerre
