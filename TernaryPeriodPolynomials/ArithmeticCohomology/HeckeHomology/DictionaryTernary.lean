module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.AssemblyConventions
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryAug
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsPrime
public import TernaryPeriodPolynomials.ArithmeticCohomology.OrdinaryCycle.Hecke.CosetsRepresentatives

@[expose] public section


/-!
# The homology Hecke operator `heckeOp (primeDatum p)` is the paper's `T₃(p,1)`, with the paper's `p²+p+1` representatives

Formalized by Claude Sonnet 5.5.
Paper: "The Hecke transfer" (representatives
`(1 0 0; 0 1 0; b c p)`, `(1 0 0; a p 0; 0 0 1)`, `diag(p,1,1)` "classify index-`p` column lattices") and `eq:Hecke-formula`.

* `primeRCEquiv`: the `p²+p+1` representatives `chartLift i` (`i : PrimeIndex p = ℤ/p × ℤ/p ⊕ ℤ/p ⊕ 1`) are a complete system of
  right cosets `S_p \ GL₃(ℤ)` of the Hecke subgroup of `primeDatum p` (the library's `primeCoset_equiv`, transported along
  `mem_S_iff_inter`).
* `gInv_chartLift`: `diag(p,1,1)⁻¹ · x_i = perm_i · h_i⁻¹` with `perm_i ∈ GL₃(ℤ)` and `h_i = primeRepresentative p i` the paper's matrix.
  Hence the coset of `diag(p,1,1)⁻¹ x_i` in `Γ\Γ diag(p,1,1)⁻¹ Γ` is `Γ h_i⁻¹`: with the right/left dictionary `ρ(h) m = m·h⁻¹` the term
  is the paper's right action `m ↦ m·h_i` (left cosets `h_i Γ` = column lattices).
* `ResHecke_prime_paper`: **degree-`q` chain-level formula**: for every projective resolution `R` and lift `lam`, the ambient operator
  `ResHecke (primeDatum p)` (whose homology is `heckeOp (primeDatum p)` by `heckeOp_resolution`) sends `[m ⊗ r]` to
  `∑_i [m·h_i ⊗ Λ_i r]`, `Λ_i = ρ(perm_i)⁻¹ ∘ lam ∘ ρ(x_i)`.
* `aug_ResHecke_prime_paper`: on `H₀`, i.e. after the augmentation `(M ⊗ R₀)_Γ → M_Γ`, it is `[m] ↦ ∑_i [m·h_i]`, the paper's
  coset sum.
* Together with `heckeOp_resolution (primeDatum p) M R lam` (`groupHomologyIso ≫ H_n(ResHecke) = heckeOp ≫ groupHomologyIso`) this identifies
  `heckeOp (primeDatum p)` in every degree `n` with the homology of the paper-form chain map.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly CategoryTheory Representation Representation.Coinvariants
open TernaryPoly.ModThreeGoodAction
open TernaryPoly.OrdinaryHeckeCosets (PrimeIndex chartLift chartPermutation primeRepresentative)
open TernaryPoly.ModThreeGoodAction in
example : True := trivial



section Ternary

open scoped Classical

variable (p : ℕ) [Fact p.Prime]

theorem mem_S_iff_inter (k : IntegralGL) :
    k ∈ (primeDatum p).S ↔ TernaryPoly.OrdinaryHeckeArithmetic.integralEquiv k ∈
      TernaryPoly.OrdinaryHeckeTransfer.intersection TernaryPoly.OrdinaryHeckeArithmetic.Gamma
        (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p) := by
  rw [TernaryPoly.OrdinaryHeckeCosets.mem_primeIntersection_iff]
  exact mem_commSubgroup_gInv p k

theorem rc_mk_eq_iff (a b : IntegralGL) :
    (Quotient.mk (QuotientGroup.rightRel (primeDatum p).S) a : RC (primeDatum p).S) = Quotient.mk _ b ↔
    (Quotient.mk (QuotientGroup.rightRel (TernaryPoly.OrdinaryHeckeTransfer.intersection
        TernaryPoly.OrdinaryHeckeArithmetic.Gamma (TernaryPoly.OrdinaryHeckeCosets.primeDiagonal p)))
        (TernaryPoly.OrdinaryHeckeArithmetic.integralEquiv a)) = Quotient.mk _ (TernaryPoly.OrdinaryHeckeArithmetic.integralEquiv b) := by
  rw [rc_eq_iff, Quotient.eq (r := QuotientGroup.rightRel _), QuotientGroup.rightRel_apply, ← map_inv, ← map_mul]
  exact mem_S_iff_inter p _

/-- **The paper's `p²+p+1` representatives are a complete system of cosets `S_p \ GL₃(ℤ)`.** -/
def primeRCEquiv : PrimeIndex p ≃ RC (primeDatum p).S :=
  Equiv.ofBijective (fun i => (Quotient.mk (QuotientGroup.rightRel (primeDatum p).S) (chartLift i) : RC (primeDatum p).S))
    ⟨fun i j h => TernaryPoly.OrdinaryHeckeCosets.primeCoset_injective p ((rc_mk_eq_iff p _ _).mp h),
     fun q => by
      induction q using Quotient.inductionOn' with
      | h k =>
        obtain ⟨i, hi⟩ := TernaryPoly.OrdinaryHeckeCosets.primeCoset_surjective p
          (Quotient.mk _ (TernaryPoly.OrdinaryHeckeArithmetic.integralEquiv k))
        exact ⟨i, (rc_mk_eq_iff p _ _).mpr hi⟩⟩

theorem gInv_chartLift (i : PrimeIndex p) :
    gInv p * OrdinaryFullAction.integral (chartLift i) =
      OrdinaryFullAction.integral (chartPermutation i) * (primeRepresentative p i)⁻¹ := by
  have h := TernaryPoly.OrdinaryHeckeCosets.inverse_coset_normalization p i
  have h2 := congrArg (fun x => x⁻¹) h
  simp only [mul_inv_rev, inv_inv] at h2
  exact h2

/-- **The chain-level Hecke operator of `T₃(p,1)` in the paper's form.**  For every projective resolution `R` and every lift `lam`
of the correspondence, the ambient operator `ResHecke` (of which `heckeOp (primeDatum p)` is the homology, `heckeOp_resolution`) is the sum over the
`p²+p+1` representatives `h_i = primeRepresentative p i` of the paper (rows `(1 0 0; 0 1 0; b c p)`, `(1 0 0; a p 0; 0 0 1)`, `diag(p,1,1)`),
each acting on the coefficient by the right action `m ↦ m · h_i = ρ(h_i⁻¹) m` and on the resolution by the chain map
`Λ_i = ρ(perm_i)⁻¹ ∘ lam ∘ ρ(x_i)`. -/
theorem ResHecke_prime_paper (M : Rep.{0} ℚ OrdinaryFullAction.GL3)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (primeDatum p) R) (q : ℕ)
    (m : Rep.res OrdinaryFullAction.integral M) (r : R.complex.X q) :
    ((ResHecke (primeDatum p) M R lam).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ i : PrimeIndex p, Coinvariants.mk ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ)
        (M.ρ (primeRepresentative p i)⁻¹ m ⊗ₜ[ℚ]
          (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) := by
  rw [ResHecke_f_mk]
  let T : IntegralGL → Coinvariants ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ) := fun y =>
    Coinvariants.mk ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ)
      (M.ρ (gInv p) ((Rep.res OrdinaryFullAction.integral M).ρ y m) ⊗ₜ[ℚ] (lam.f q).hom ((R.complex.X q).ρ y r))
  have hT : ∀ (s : (primeDatum p).S) (y : IntegralGL), T ((s : IntegralGL) * y) = T y := by
    intro s y
    have hf := (primeDatum p).hf s
    have e1 : M.ρ (gInv p) ((Rep.res OrdinaryFullAction.integral M).ρ ((s : IntegralGL) * y) m) =
        (Rep.res OrdinaryFullAction.integral M).ρ ((primeDatum p).f s)
          (M.ρ (gInv p) ((Rep.res OrdinaryFullAction.integral M).ρ y m)) := by
      change M.ρ (gInv p) (M.ρ (OrdinaryFullAction.integral ((s : IntegralGL) * y)) m) =
        M.ρ (OrdinaryFullAction.integral ((primeDatum p).f s)) (M.ρ (gInv p) (M.ρ (OrdinaryFullAction.integral y) m))
      have h : ∀ (a b : OrdinaryFullAction.GL3) (v : M), M.ρ a (M.ρ b v) = M.ρ (a * b) v := fun a b v => by
        rw [map_mul]; rfl
      have key : gInv p * OrdinaryFullAction.integral ((s : IntegralGL) * y) =
          OrdinaryFullAction.integral ((primeDatum p).f s) * (gInv p * OrdinaryFullAction.integral y) := by
        rw [hf, map_mul]; group
      simp only [h]
      rw [key]
    have e2 : (lam.f q).hom ((R.complex.X q).ρ ((s : IntegralGL) * y) r) =
        (R.complex.X q).ρ ((primeDatum p).f s) ((lam.f q).hom ((R.complex.X q).ρ y r)) := by
      rw [map_mul]
      exact Rep.hom_comm_apply (lam.f q) s _
    simp only [T]
    rw [e1, e2]
    exact Coinvariants.mk_self_apply ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ)
      ((primeDatum p).f s) (M.ρ (gInv p) ((Rep.res OrdinaryFullAction.integral M).ρ y m) ⊗ₜ[ℚ]
        (lam.f q).hom ((R.complex.X q).ρ y r))
  have h1 : ∑ x : RC (primeDatum p).S, T x.out = ∑ i : PrimeIndex p, T (chartLift i) := by
    rw [← Equiv.sum_comp (primeRCEquiv p) (fun x : RC (primeDatum p).S => T x.out)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq : (Quotient.mk (QuotientGroup.rightRel (primeDatum p).S) ((primeRCEquiv p i).out) : RC (primeDatum p).S) =
        Quotient.mk _ (chartLift i) := Quotient.out_eq _
    have hm := (rc_eq_iff (primeDatum p).S _ _).mp hq
    have : chartLift i = (chartLift i * ((primeRCEquiv p i).out)⁻¹) * (primeRCEquiv p i).out := by group
    conv_rhs => rw [this]
    exact (hT ⟨_, hm⟩ _).symm
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [T]
  have e3 : M.ρ (gInv p) ((Rep.res OrdinaryFullAction.integral M).ρ (chartLift i) m) =
      (Rep.res OrdinaryFullAction.integral M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) := by
    change M.ρ (gInv p) (M.ρ (OrdinaryFullAction.integral (chartLift i)) m) =
      M.ρ (OrdinaryFullAction.integral (chartPermutation i)) (M.ρ (primeRepresentative p i)⁻¹ m)
    have h : ∀ (a b : OrdinaryFullAction.GL3) (v : M), M.ρ a (M.ρ b v) = M.ρ (a * b) v := fun a b v => by
      rw [map_mul]; rfl
    rw [h, h, gInv_chartLift]
  rw [e3]
  have hk : ∀ b : R.complex.X q, (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹ b) = b := by
    intro b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have e4 : (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹
      ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) = (lam.f q).hom ((R.complex.X q).ρ (chartLift i) r) :=
    hk _
  have e5 := Coinvariants.mk_self_apply ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ)
    (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m ⊗ₜ[ℚ]
      (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r)))
  refine Eq.trans ?_ e5
  change Coinvariants.mk _ ((Rep.res OrdinaryFullAction.integral M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) ⊗ₜ[ℚ]
      (lam.f q).hom ((R.complex.X q).ρ (chartLift i) r)) = Coinvariants.mk _
    ((Rep.res OrdinaryFullAction.integral M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) ⊗ₜ[ℚ]
      (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹
        ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))))
  rw [e4]

theorem aug_ResHecke_prime_paper (M : Rep.{0} ℚ OrdinaryFullAction.GL3)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (primeDatum p) R)
    (hlam : LiftOverId (primeDatum p) R lam)
    (m : Rep.res OrdinaryFullAction.integral M) (r : R.complex.X 0) :
    augMap (Rep.res OrdinaryFullAction.integral M) (R.complex.X 0) (epsOf R)
        (((ResHecke (primeDatum p) M R lam).f 0).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r))) =
      (epsOf R).hom r • ∑ i : PrimeIndex p, Coinvariants.mk (Rep.res OrdinaryFullAction.integral M).ρ
        (M.ρ (primeRepresentative p i)⁻¹ m) := by
  rw [ResHecke_prime_paper, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [augMap_mk]
  congr 1
  have e1 : ∀ (g : IntegralGL) (v : R.complex.X 0), (epsOf R).hom ((R.complex.X 0).ρ g v) = (epsOf R).hom v :=
    fun g v => Rep.hom_comm_apply (epsOf R) g v
  have e2 : ∀ v : R.complex.X 0, (epsOf R).hom ((lam.f 0).hom v) = (epsOf R).hom v :=
    fun v => congrArg (fun t => t.hom v) hlam
  exact (e1 _ _).trans ((e2 _).trans (e1 _ _))

/-- `ResHecke_prime_paper` with the paper's right action `m · h_i` written out. -/
theorem ResHecke_prime_paper_right (M : Rep.{0} ℚ OrdinaryFullAction.GL3)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (primeDatum p) R) (q : ℕ)
    (m : Rep.res OrdinaryFullAction.integral M) (r : R.complex.X q) :
    ((ResHecke (primeDatum p) M R lam).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ i : PrimeIndex p, Coinvariants.mk ((Rep.res OrdinaryFullAction.integral M).ρ.tprod (R.complex.X q).ρ)
        (rightAct M m (primeRepresentative p i) ⊗ₜ[ℚ]
          (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) :=
  ResHecke_prime_paper p M R lam q m r

end Ternary

end TernaryPeriodPolynomials.Argument.HeckeHomology
