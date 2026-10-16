module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftSums
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftReindex
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftData
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeLiftFinite

@[expose] public section


/-!
# The edge-coefficient formula for the homology Hecke operator (L5)

Formalized by Claude Sonnet 5.5.

* `edge2_hecke_formula`: `2 nP · edge2 (T y) = ∑_X SS (ε ↦ ε⁻¹ g X y) (λ₁ (X E₀))`, from the comparison-theorem
  description of the Hecke operator (`heckeOp_H1Iso`);
* `Tfun`, `Tfun_inv`, `Tfun_support_*`, `lhs_sum`, `rhs_sum`: the double-sum kernel and its invariance and finiteness;
* `L5_holds`: `(TΦ)(E₀) = homT s Φ E₀` for a Frobenius datum, a transposed lift over the identity.
-/

open CategoryTheory Representation

noncomputable section
open scoped Classical

namespace TernaryPeriodPolynomials.Argument.HeckeNormalization

section Cycle

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.BinaryDuality

theorem mk_E0 (M : Rep ℚ IntegralGL) (b : M) (hb : M.ρ sOne b = -b) :
    (Coinvariants.mk _ (b ⊗ₜ[ℚ] ((E0 : P1) : PE)) : CT M PE) = (2 : ℚ) • genP M b := by
  have h1 : (Coinvariants.mk _ (b ⊗ₜ[ℚ] MonoidAlgebra.single p0.swap (1 : ℚ)) : CT M PE) = (sigC M).hom (genP M b) := by
    change _ = Coinvariants.mk _ (b ⊗ₜ[ℚ] swapMap.hom (MonoidAlgebra.single p0 (1 : ℚ)))
    rw [swapMap_single]
  rw [sigC_genP, hb] at h1
  have hE : ((E0 : P1) : PE) = MonoidAlgebra.single p0 (1 : ℚ) - MonoidAlgebra.single p0.swap (1 : ℚ) := rfl
  rw [hE, TensorProduct.tmul_sub, map_sub, h1, map_neg]
  change genP M b - (-genP M b) = _
  module

theorem cycle_gen (M : Rep ℚ IntegralGL) (x : groupHomology M 1) :
    (((H1Iso M).hom.hom x : LinearMap.ker (dC M).hom) : CT M P1) =
      ((2 * nP : ℚ))⁻¹ • (Coinvariants.mk _ (edge2 M x ⊗ₜ[ℚ] E0) : CT M P1) := by
  apply inclC_injective M
  set z := (((H1Iso M).hom.hom x : LinearMap.ker (dC M).hom) : CT M P1) with hz
  have hb : edge2 M x = evalP M ((inclC M).hom z) := rfl
  have hn := nP_smul_eq M ((inclC M).hom z)
  have hanti := (edge2_isEdgeCoeff M x).anti
  rw [map_smul]
  have h1 : (inclC M).hom (Coinvariants.mk _ (edge2 M x ⊗ₜ[ℚ] E0) : CT M P1) =
      (Coinvariants.mk _ (edge2 M x ⊗ₜ[ℚ] ((E0 : P1) : PE)) : CT M PE) := rfl
  rw [h1, mk_E0 M _ hanti]
  have hn' : (nP : ℚ) • (inclC M).hom z = genP M (edge2 M x) := by rw [hb]; exact hn
  have hnp := nP_pos
  have e1 : (inclC M).hom z = ((nP : ℚ))⁻¹ • genP M (edge2 M x) := by
    rw [← hn', smul_smul, inv_mul_cancel₀ hnp, one_smul]
  rw [e1, smul_smul]
  congr 1
  field_simp

end Cycle

section Hecke

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPeriodPolynomials.Argument.HeckeDuality
open TernaryPeriodPolynomials.Argument.HeckeHomology
open TernaryPeriodPolynomials.Argument.HeckeNormalization.BridgeInterface
open TernaryPoly.RankTwoAugmentedFrames TernaryPoly.BinaryModularSymbol
open TernaryPeriodPolynomials.Argument.BinaryDuality

variable (p : ℕ) [Fact p.Prime]

theorem edge2_hecke_formula (M : Rep.{0} ℚ GL2) (l : LiftData p) (hid : l.OverId)
    (y : groupHomology (Rep.res binIota M) 1) :
    (2 * nP : ℚ) • edge2 (Rep.res binIota M) ((heckeOp (binDatum p) M 1).hom y) =
      ∑ X : RC (binDatum p).S,
        SS (fun ε => (Rep.res binIota M).ρ ε⁻¹ (M.ρ (C1 p) ((Rep.res binIota M).ρ (Quotient.out X)
          (edge2 (Rep.res binIota M) y))))
          ((l.lam1 (P1.ρ (Quotient.out X) E0) : P1) : PE) := by
  set lam := liftOfData p l with hlam
  have hH := heckeOp_H1Iso (binDatum p) M lam (liftOfData_overId p l hid) (binDatum_hproj p)
  have h1 := congrArg (fun φ => ((φ.hom y : LinearMap.ker (dC (Rep.res binIota M)).hom) :
    CT (Rep.res binIota M) P1)) hH
  simp only [ModuleCat.hom_comp] at h1
  have e1 : edge2 (Rep.res binIota M) ((heckeOp (binDatum p) M 1).hom y) =
      evalP (Rep.res binIota M) ((inclC (Rep.res binIota M)).hom
        (((ResHecke (binDatum p) M farResolution lam).f 1).hom
          (((H1Iso (Rep.res binIota M)).hom.hom y : LinearMap.ker (dC (Rep.res binIota M)).hom) :
            CT (Rep.res binIota M) P1))) := by
    have h2 : (((H1Iso (Rep.res binIota M)).hom.hom ((heckeOp (binDatum p) M 1).hom y) :
        LinearMap.ker (dC (Rep.res binIota M)).hom) : CT (Rep.res binIota M) P1) =
        ((ResHecke (binDatum p) M farResolution lam).f 1).hom
          (((H1Iso (Rep.res binIota M)).hom.hom y : LinearMap.ker (dC (Rep.res binIota M)).hom) :
            CT (Rep.res binIota M) P1) := h1
    exact congrArg (fun z => evalP (Rep.res binIota M) ((inclC (Rep.res binIota M)).hom z)) h2
  rw [e1, cycle_gen]
  erw [map_smul, map_smul, map_smul]
  have hnz : (2 * (nP : ℚ)) ≠ 0 := mul_ne_zero two_ne_zero nP_pos
  rw [smul_smul, mul_inv_cancel₀ hnz, one_smul]
  erw [ResHecke_f_mk (binDatum p) M farResolution lam 1]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun X _ => ?_
  exact evalP_mk_eq (Rep.res binIota M) _ _

omit [Fact p.Prime] in
theorem SS_smul_F {N : Type*} [AddCommGroup N] [Module ℚ N] (r : ℚ) (F : IntegralGL → N) (c : PE) :
    r • SS F c = SS (fun ε => r • F ε) c := by
  unfold SS
  rw [smul_finsum' _ (finite_support_coeff c F)]
  refine finsum_congr fun ε => ?_
  rw [smul_comm]

/-- The kernel `T` of the double sum. -/
def Tfun (s : DualLift p) (d : ℕ) (B : Dplain d) (y x : IntegralGL) : Dplain d :=
  (((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE).coeff (x • p0)) •
    (binMod d).ρ (binIota y * C1 p * binIota x) B

theorem Tfun_inv (s : DualLift p) (d : ℕ) (B : Dplain d) (σ : (binDatum p).S) (y x : IntegralGL) :
    Tfun p s d B (y * (binDatum p).f σ) ((σ : IntegralGL)⁻¹ * x) = Tfun p s d B y x := by
  unfold Tfun
  have e1 : P1.ρ (y * (binDatum p).f σ)⁻¹ E0 = P1.ρ ((binDatum p).f σ)⁻¹ (P1.ρ y⁻¹ E0) := by
    rw [mul_inv_rev, map_mul]; rfl
  have e2 : s.s1 (P1.ρ ((binDatum p).f σ)⁻¹ (P1.ρ y⁻¹ E0)) = P1.ρ (σ : IntegralGL)⁻¹ (s.s1 (P1.ρ y⁻¹ E0)) := by
    have := s.eq1 σ⁻¹ (P1.ρ y⁻¹ E0)
    rw [map_inv] at this
    exact this
  rw [e1, e2]
  have e3 : ((P1.ρ (σ : IntegralGL)⁻¹ (s.s1 (P1.ρ y⁻¹ E0)) : P1) : PE).coeff (((σ : IntegralGL)⁻¹ * x) • p0) =
      ((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE).coeff (x • p0) := by
    change (PE.ρ (σ : IntegralGL)⁻¹ ((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE)).coeff _ = _
    rw [coeff_PE_ρ, inv_inv, mul_smul, smul_inv_smul]
  have e4 : binIota (y * (binDatum p).f σ) * C1 p * binIota ((σ : IntegralGL)⁻¹ * x) =
      binIota y * C1 p * binIota x := by
    simp only [map_mul, map_inv]
    rw [(binDatum p).hf σ]
    group
  rw [e3, e4]

theorem Tfun_support_y (s : DualLift p) (l : LiftData p) (h : l.IsAdjoint s) (d : ℕ) (B : Dplain d)
    (x : IntegralGL) : (Function.support fun y => Tfun p s d B y x).Finite := by
  have hfin : (Set.Finite ((fun γ : IntegralGL => γ⁻¹) ''
      ⋃ e ∈ ((l.lam1 (EeP (x • p0)) : P1) : PE).coeff.support, fiberE e)) :=
    ((Finset.finite_toSet _).biUnion fun e _ => fiberE_finite e).image _
  refine hfin.subset ?_
  intro y hy
  simp only [Function.mem_support, ne_eq] at hy
  have hc : ((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE).coeff (x • p0) ≠ 0 := by
    intro h0
    apply hy
    unfold Tfun
    exact (congrArg (fun r : ℚ => r • (binMod d).ρ (binIota y * C1 p * binIota x) B) h0).trans (zero_smul ℚ _)
  rw [E0_eq, EeP_ρ] at hc
  have e := adj_coeff s l h (y⁻¹ • p0) (x • p0)
  change ((l.lam1 (EeP (x • p0)) : P1) : PE).coeff (y⁻¹ • p0) =
    ((s.s1 (EeP (y⁻¹ • p0)) : P1) : PE).coeff (x • p0) at e
  rw [← e] at hc
  refine ⟨y⁻¹, ?_, inv_inv y⟩
  simp only [Set.mem_iUnion]
  exact ⟨y⁻¹ • p0, Finsupp.mem_support_iff.mpr hc, rfl⟩

theorem Tfun_support_x (s : DualLift p) (d : ℕ) (B : Dplain d) (y : IntegralGL) :
    (Function.support fun x => Tfun p s d B y x).Finite := by
  refine ((Finset.finite_toSet ((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE).coeff.support).biUnion
    fun e _ => fiberE_finite e).subset ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  have hc : ((s.s1 (P1.ρ y⁻¹ E0) : P1) : PE).coeff (x • p0) ≠ 0 := by
    intro h0
    apply hx
    unfold Tfun
    exact (congrArg (fun r : ℚ => r • (binMod d).ρ (binIota y * C1 p * binIota x) B) h0).trans (zero_smul ℚ _)
  simp only [Set.mem_iUnion, Finset.mem_coe]
  exact ⟨x • p0, Finsupp.mem_support_iff.mpr hc, rfl⟩

theorem rho_comp_left (d : ℕ) (B : Dplain d) (ε x : IntegralGL) :
    (Dplain d).ρ ε ((binMod d).ρ (C1 p) ((Dplain d).ρ x B)) =
      (binMod d).ρ (binIota ε * C1 p * binIota x) B := by
  simp only [map_mul]
  rfl

theorem lhs_sum (s : DualLift p) (l : LiftData p) (h : l.IsAdjoint s) (d : ℕ) (B : Dplain d) (x : IntegralGL) :
    SS (fun ε => (Dplain d).ρ ε⁻¹ ((binMod d).ρ (C1 p) ((Dplain d).ρ x B)))
        ((l.lam1 (P1.ρ x E0) : P1) : PE) = ∑ᶠ y, Tfun p s d B y x := by
  unfold SS
  rw [← finsum_comp_equiv (Equiv.inv IntegralGL)]
  refine finsum_congr fun ε => ?_
  have e : ((l.lam1 (P1.ρ x E0) : P1) : PE).coeff (ε⁻¹ • p0) =
      ((s.s1 (P1.ρ ε⁻¹ E0) : P1) : PE).coeff (x • p0) := by
    rw [E0_eq, EeP_ρ, EeP_ρ]
    exact adj_coeff s l h (ε⁻¹ • p0) (x • p0)
  unfold Tfun
  simp only [Equiv.inv_apply, inv_inv]
  rw [e]
  have := rho_comp_left p d B ε x
  exact congrArg (fun z => ((s.s1 (P1.ρ ε⁻¹ E0) : P1) : PE).coeff (x • p0) • z) this

theorem rhs_sum (s : DualLift p) (d : ℕ) (B : Dplain d) (Y : IntegralGL) :
    (binMod d).ρ (binIota Y * C1 p) (SS (fun ε => (Dplain d).ρ ε B) ((s.s1 (P1.ρ Y⁻¹ E0) : P1) : PE)) =
      ∑ᶠ x, Tfun p s d B Y x := by
  refine (SS_map ((binMod d).ρ (binIota Y * C1 p)) (fun ε => (Dplain d).ρ ε B) _).trans ?_
  unfold SS
  refine finsum_congr fun x => ?_
  unfold Tfun
  have h1 : (binMod d).ρ (binIota Y * C1 p) ((Dplain d).ρ x B) =
      (binMod d).ρ (binIota Y * C1 p * binIota x) B := by
    simp only [map_mul]
    rfl
  exact congrArg (fun z => ((s.s1 (P1.ρ Y⁻¹ E0) : P1) : PE).coeff (x • p0) • z) h1

theorem L5_holds (d : ℕ) : BridgeInterface.L5 p d := by
  intro F s l hadj hid y
  have hfin := finite_quot_f_range p
  have hnz : (2 * (nP : ℚ)) ≠ 0 := mul_ne_zero two_ne_zero nP_pos
  have hΦ := (F.frob y).2.1
  have hκ1 := F.eval y
  have hκ2 := F.eval ((heckeOp (binDatum p) (binMod d) 1).hom y)
  apply smul_right_injective _ hnz
  have hfi : Fintype (IntegralGL ⧸ (binDatum p).f.range) := Fintype.ofFinite _
  have hR : (2 * (nP : ℚ)) • homT p s d ((F.frob y : PhiSp d) : P1 →ₗ[ℚ] Dplain d) E0 =
      ∑ᶠ Y : IntegralGL ⧸ (binDatum p).f.range, ∑ᶠ x, Tfun p s d (((F.frob y : PhiSp d) : P1 →ₗ[ℚ] Dplain d) E0)
        (Quotient.out Y) x := by
    let Φ : P1 →ₗ[ℚ] Dplain d := ((F.frob y : PhiSp d) : P1 →ₗ[ℚ] Dplain d)
    let G : IntegralGL ⧸ (binDatum p).f.range → Dplain d := fun Y =>
      (binMod d).ρ (binIota (Quotient.out Y) * C1 p) (Φ (s.s1 (P1.ρ (Quotient.out Y)⁻¹ E0)))
    have step : ∀ Y : IntegralGL ⧸ (binDatum p).f.range, (2 * (nP : ℚ)) • G Y =
        ∑ᶠ x, Tfun p s d (Φ E0) (Quotient.out Y) x := by
      intro Y
      have h1 := LinearMap.map_smul ((binMod d).ρ (binIota (Quotient.out Y) * C1 p)) (2 * (nP : ℚ))
        (Φ (s.s1 (P1.ρ (Quotient.out Y)⁻¹ E0)) : binMod d)
      have h2 := phi_formula (Dplain d) Φ hΦ (s.s1 (P1.ρ (Quotient.out Y)⁻¹ E0))
      exact h1.symm.trans ((congrArg (fun v => (binMod d).ρ (binIota (Quotient.out Y) * C1 p) v) h2).trans
        (rhs_sum p s d (Φ E0) (Quotient.out Y)))
    calc (2 * (nP : ℚ)) • homT p s d Φ E0
        = (2 * (nP : ℚ)) • ∑ᶠ Y, G Y := rfl
      _ = ∑ᶠ Y, (2 * (nP : ℚ)) • G Y := smul_finsum' _ (Set.toFinite _)
      _ = ∑ᶠ Y : IntegralGL ⧸ (binDatum p).f.range, ∑ᶠ x, Tfun p s d (Φ E0) (Quotient.out Y) x :=
          finsum_congr step
  have hL : (2 * (nP : ℚ)) • ((F.frob ((heckeOp (binDatum p) (binMod d) 1).hom y) : PhiSp d) :
      P1 →ₗ[ℚ] Dplain d) E0 =
      ∑ X : RC (binDatum p).S, ∑ᶠ y' : IntegralGL, Tfun p s d (((F.frob y : PhiSp d) : P1 →ₗ[ℚ] Dplain d) E0) y'
        (Quotient.out X) := by
    have hE := edge2_hecke_formula p (binMod d) l hid y
    have key : ∀ (X : RC (binDatum p).S), ∑ᶠ y' : IntegralGL, Tfun p s d
        (((F.frob y : PhiSp d) : P1 →ₗ[ℚ] Dplain d) E0) y' (Quotient.out X) =
        F.κ • SS (fun ε => (Dplain d).ρ ε⁻¹ ((binMod d).ρ (C1 p) ((Dplain d).ρ (Quotient.out X)
          (edge2 (Dplain d) y)))) ((l.lam1 (P1.ρ (Quotient.out X) E0) : P1) : PE) := by
      intro X
      rw [← lhs_sum p s l hadj d _ (Quotient.out X), SS_smul_F]
      refine congrArg (fun G => SS G ((l.lam1 (P1.ρ (Quotient.out X) E0) : P1) : PE)) (funext fun ε => ?_)
      rw [hκ1]
      have e1 := LinearMap.map_smul ((Dplain d).ρ (Quotient.out X)) F.κ (edge2 (Dplain d) y)
      have e2 := LinearMap.map_smul ((binMod d).ρ (C1 p)) F.κ
        ((Dplain d).ρ (Quotient.out X) (edge2 (Dplain d) y))
      have e3 := LinearMap.map_smul ((Dplain d).ρ ε⁻¹) F.κ
        ((binMod d).ρ (C1 p) ((Dplain d).ρ (Quotient.out X) (edge2 (Dplain d) y)))
      exact (congrArg (fun v => (Dplain d).ρ ε⁻¹ ((binMod d).ρ (C1 p) v)) e1).trans
        ((congrArg ((Dplain d).ρ ε⁻¹) e2).trans e3)
    have h3 : (2 * (nP : ℚ)) • F.κ • edge2 (Dplain d) ((heckeOp (binDatum p) (binMod d) 1).hom y) =
        F.κ • ((2 * (nP : ℚ)) • edge2 (Dplain d) ((heckeOp (binDatum p) (binMod d) 1).hom y)) :=
      smul_comm _ _ _
    calc (2 * (nP : ℚ)) • ((F.frob ((heckeOp (binDatum p) (binMod d) 1).hom y) : PhiSp d) :
          P1 →ₗ[ℚ] Dplain d) E0
        = (2 * (nP : ℚ)) • F.κ • edge2 (Dplain d) ((heckeOp (binDatum p) (binMod d) 1).hom y) :=
          congrArg (fun v => (2 * (nP : ℚ)) • v) hκ2
      _ = F.κ • ((2 * (nP : ℚ)) • edge2 (Dplain d) ((heckeOp (binDatum p) (binMod d) 1).hom y)) := h3
      _ = F.κ • ∑ X : RC (binDatum p).S, SS (fun ε => (Dplain d).ρ ε⁻¹ ((binMod d).ρ (C1 p)
            ((Dplain d).ρ (Quotient.out X) (edge2 (Dplain d) y))))
            ((l.lam1 (P1.ρ (Quotient.out X) E0) : P1) : PE) := congrArg (fun v => F.κ • v) hE
      _ = ∑ X : RC (binDatum p).S, F.κ • SS (fun ε => (Dplain d).ρ ε⁻¹ ((binMod d).ρ (C1 p)
            ((Dplain d).ρ (Quotient.out X) (edge2 (Dplain d) y))))
            ((l.lam1 (P1.ρ (Quotient.out X) E0) : P1) : PE) := Finset.smul_sum
      _ = _ := Finset.sum_congr rfl fun X _ => (key X).symm
  show (2 * (nP : ℚ)) • _ = (2 * (nP : ℚ)) • _
  rw [hR, hL]
  exact sum_reindex (binDatum p).S (binDatum p).f (binDatum_f_injective p) _
    (fun σ y x => Tfun_inv p s d _ σ y x) (fun x => Tfun_support_y p s l hadj d _ x)
    (fun y => Tfun_support_x p s d _ y)

end Hecke

end TernaryPeriodPolynomials.Argument.HeckeNormalization
