module

public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Analytic
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.ResolutionModelFarey
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobenius
public import TernaryPeriodPolynomials.SymmetricSolution.FiniteDifference.Symbol

@[expose] public section

/-!
# Lemma B.1, period clause: naturality of the period symbol in the coefficients

Formalized by Claude Sonnet 5.5.

For a morphism `φ : M ⟶ N` of `ℚ`-representations of `GL₂(ℤ)` (e.g. the complexification `cInc d : Sym^d ⟶ Sym^d ⊗ ℂ`) and
`φ_* = groupHomology.map (MonoidHom.id _) φ 1`:
* `gF_natural`: the Farey model `groupHomologyFarey` is natural for the chain map `farMap φ` (`groupHomologyIso_PhiMap` with `f = id`);
* `H1Iso_natural`, `h1Raw_natural`, `frobM_natural`: the Farey cycle, its Frobenius function and the form `Φ` are natural;
* `symbolEquiv_natural`: `σ_{φ_* x} = φ ∘ σ_x`; `edge2_natural`: `edge₂ (φ_* x) = φ (edge₂ x)`.
-/

noncomputable section
open CategoryTheory TernaryPoly.RankTwoAugmentedFrames TernaryPeriodPolynomials.Argument.FareyTree
  TernaryPeriodPolynomials.Argument.HeckeHomology Representation
open TernaryPeriodPolynomials.Argument.BinaryDuality TernaryPeriodPolynomials.Argument.HeckeNormalization
open TernaryPoly.BinaryModularSymbol TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPeriodPolynomials.Argument.HeckeDuality
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.LemmaB1Period

variable {M N : Rep ℚ IntegralGL} (φ : M ⟶ N)

/-- The chain map induced by `φ` on the Farey complexes of coinvariants. -/
def farMap : farResolution.complex.coinvariantsTensorObj M ⟶ farResolution.complex.coinvariantsTensorObj N :=
  PhiMap (MonoidHom.id IntegralGL) φ (𝟙 farResolution.complex)

theorem gF_natural (n : ℕ) :
    (groupHomologyFarey M n).hom ≫ HomologicalComplex.homologyMap (farMap φ) n =
      groupHomology.map (MonoidHom.id IntegralGL) φ n ≫ (groupHomologyFarey N n).hom :=
  groupHomologyIso_PhiMap (MonoidHom.id IntegralGL) φ farResolution (fun q => farProjective q) farResolution (𝟙 _) rfl n

theorem farMap_f_mk (m : M) (p : P1) :
    ((farMap φ).f 1).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] p)) = Coinvariants.mk _ (φ.hom m ⊗ₜ[ℚ] p) := rfl

theorem homologyMap_H1lift_natural :
    HomologicalComplex.homologyMap (farMap φ) 1 ≫ H1lift N = H1lift M ≫ (farMap φ).f 1 := by
  refine (cancel_epi ((farResolution.complex.coinvariantsTensorObj M).homologyπ 1)).1 ?_
  rw [HomologicalComplex.homologyπ_naturality_assoc, homologyπ_H1lift, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, homologyπ_H1lift]

theorem gF_H1lift : (groupHomologyFarey M 1).hom ≫ H1lift M = (H1Iso M).hom ≫ kerIncl M := by
  unfold H1lift
  rw [Iso.hom_inv_id_assoc]

theorem H1lift_gF (x : groupHomology M 1) :
    (H1lift M).hom ((groupHomologyFarey M 1).hom.hom x) = (((H1Iso M).hom.hom x : LinearMap.ker (dC M).hom) : CT M P1) :=
  congrArg (fun f => f.hom x) (gF_H1lift (M := M))

theorem H1Iso_natural (x : groupHomology M 1) :
    (((H1Iso N).hom.hom ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) : LinearMap.ker (dC N).hom) : CT N P1) =
      ((farMap φ).f 1).hom (((H1Iso M).hom.hom x : LinearMap.ker (dC M).hom) : CT M P1) := by
  rw [← H1lift_gF, ← H1lift_gF]
  have h1 := congrArg (fun f => f.hom x) (gF_natural φ 1)
  have h2 := congrArg (fun f => f.hom ((groupHomologyFarey M 1).hom.hom x)) (homologyMap_H1lift_natural φ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [← h1]
  exact h2

theorem normAt_natural {X : Type} [MulAction IntegralGL X] {x₀ : X} (hx : Finite (MulAction.stabilizer IntegralGL x₀))
    (y : X) (m : M) : normAt hx N y (φ.hom m) = φ.hom (normAt hx M y m) := by
  unfold normAt
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun γ _ => (Rep.hom_comm_apply φ γ m).symm

theorem frobE_natural (w : CT M PE) (e : OTE) :
    (frobE N ((WMap (MonoidHom.id IntegralGL) φ PE).hom w) : OTE → N) e = φ.hom ((frobE M w : OTE → M) e) := by
  rw [frobE_apply, frobE_apply]
  have key : (evalAt (ote_stabilizer_finite e) N) ∘ₗ (WMap (MonoidHom.id IntegralGL) φ PE).hom =
      φ.hom.toLinearMap ∘ₗ evalAt (ote_stabilizer_finite e) M := by
    apply ct_ext
    intro m y r
    change evalAt (ote_stabilizer_finite e) N (Coinvariants.mk _ (φ.hom m ⊗ₜ[ℚ] MonoidAlgebra.single y r)) =
      φ.hom (evalAt (ote_stabilizer_finite e) M (Coinvariants.mk _ (m ⊗ₜ[ℚ] MonoidAlgebra.single y r)))
    rw [evalAt_mk, evalAt_mk, evalTen_tmul_single, evalTen_tmul_single, normAt_natural, map_smul]
  exact LinearMap.congr_fun key w


theorem hom_ext_CT {P : Rep ℚ IntegralGL} {A : Type} [AddCommGroup A] [Module ℚ A]
    (L1 L2 : Coinvariants ((M.ρ).tprod P.ρ) →ₗ[ℚ] A)
    (h : ∀ (m : M) (p : P), L1 (Coinvariants.mk _ (m ⊗ₜ p)) = L2 (Coinvariants.mk _ (m ⊗ₜ p))) : L1 = L2 :=
  Coinvariants.hom_ext (TensorProduct.ext' fun m p => h m p)

theorem inclC_natural (z : CT M P1) :
    (inclC N).hom ((WMap (MonoidHom.id IntegralGL) φ P1).hom z) =
      (WMap (MonoidHom.id IntegralGL) φ PE).hom ((inclC M).hom z) := by
  have key : (inclC N).hom ∘ₗ (WMap (MonoidHom.id IntegralGL) φ P1).hom =
      (WMap (MonoidHom.id IntegralGL) φ PE).hom ∘ₗ (inclC M).hom := by
    apply hom_ext_CT
    intro m p
    rfl
  exact LinearMap.congr_fun key z

theorem farMap_f1 (z : CT M P1) : ((farMap φ).f 1).hom z = (WMap (MonoidHom.id IntegralGL) φ P1).hom z := by
  have key : ((farMap φ).f 1).hom = (WMap (MonoidHom.id IntegralGL) φ P1).hom := by
    apply hom_ext_CT
    intro m p
    rfl
  exact LinearMap.congr_fun key z

theorem h1Raw_natural (x : groupHomology M 1) (e : OTE) :
    ((h1Raw N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) : EqFun (Γ := IntegralGL) OTE N) : OTE → N) e =
      φ.hom (((h1Raw M x : EqFun (Γ := IntegralGL) OTE M) : OTE → M) e) := by
  change (frobE N ((inclC N).hom (((H1Iso N).hom.hom ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) :
      LinearMap.ker (dC N).hom) : CT N P1)) : OTE → N) e = φ.hom ((frobE M ((inclC M).hom (((H1Iso M).hom.hom x :
      LinearMap.ker (dC M).hom) : CT M P1)) : OTE → M) e)
  rw [H1Iso_natural, farMap_f1, inclC_natural, frobE_natural]


theorem frobM_natural (x : groupHomology M 1) (y : P1) :
    ((frobM N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) : PhiM N) : P1 →ₗ[ℚ] N) y =
      φ.hom (((frobM M x : PhiM M) : P1 →ₗ[ℚ] M) y) := by
  have key : ((frobM N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) : PhiM N) : P1 →ₗ[ℚ] N) =
      φ.hom.toLinearMap ∘ₗ ((frobM M x : PhiM M) : P1 →ₗ[ℚ] M) := by
    apply P1_hom_ext
    intro e
    change phiOf N (h1Fun N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x)).1 (Ee e) =
      φ.hom (phiOf M (h1Fun M x).1 (Ee e))
    rw [phiOf_Ee, phiOf_Ee, map_sub]
    exact congrArg₂ (· - ·) (h1Raw_natural φ x e) (h1Raw_natural φ x e.swap)
  exact LinearMap.congr_fun key y

theorem symbolEquiv_natural (x : groupHomology M 1) :
    ((symbolEquiv N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) : SymHom N) : St →ₗ[ℚ] N) =
      φ.hom.toLinearMap ∘ₗ ((symbolEquiv M x : SymHom M) : St →ₗ[ℚ] M) := by
  apply LinearMap.ext
  intro c
  obtain ⟨y, rfl⟩ := piL_surjective c
  rw [symbolEquiv_piL, frobM_natural, LinearMap.comp_apply, symbolEquiv_piL]
  rfl

theorem edge2_natural (x : groupHomology M 1) :
    edge2 N ((groupHomology.map (MonoidHom.id IntegralGL) φ 1).hom x) = φ.hom (edge2 M x) := by
  rw [← symbolEquiv_reference, symbolEquiv_natural, LinearMap.comp_apply, symbolEquiv_reference]
  rfl

end TernaryPeriodPolynomials.Argument.LemmaB1Period
