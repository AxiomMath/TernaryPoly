module

public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.AssemblyConventions
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeHomology.DictionaryAug
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Cosets
public import TernaryPeriodPolynomials.PeriodPolynomial.RationalHecke.Prime.Representatives

@[expose] public section


/-!
# The homology Hecke operator `heckeOp (binDatum p)` is the paper's binary `T₂(p)`, with the paper's `p+1` representatives

Formalized by Claude Sonnet 5.5.
Paper: (`C_c = (1 0; c p)`, `0 ≤ c < p`, `C_∞ = diag(p,1)`; "the brackets
denote the usual binary double-coset correspondences").

Binary analogue of `DictionaryTernary`: `primeRCEquivBin` (the `p+1` representatives are a complete system of cosets `Γ₀(p) \ GL₂(ℤ)`),
`C1_chartLift` (`diag(1/p,1) · x_i = perm_i · C_i⁻¹`, `C_i` the paper's matrix), `ResHecke_prime_paper_bin` (chain level, any resolution),
`aug_ResHecke_prime_paper_bin` (`H₀`/coinvariants: `[m] ↦ ∑_i [m·C_i]`, the right action `m·C = ρ(C⁻¹)m`).
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.HeckeHomology

open TernaryPoly CategoryTheory Representation Representation.Coinvariants
open TernaryPoly.RankTwoAugmentedFrames
open TernaryPoly.BinaryRationalHeckePrime (PrimeIndex chartLift chartPermutation primeRepresentative)

section Binary

open scoped Classical

variable (p : ℕ) [Fact p.Prime]

theorem C1_eq_inv : C1 p = (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)⁻¹ := by
  apply Units.ext
  rfl

theorem mem_S_iff_inter_bin (k : IntegralGL) :
    k ∈ (binDatum p).S ↔ TernaryPoly.BinaryRationalHeckeArithmetic.integralEquiv k ∈
      TernaryPoly.OrdinaryHeckeTransfer.intersection TernaryPoly.BinaryRationalHeckeArithmetic.Gamma
        (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p) := by
  rw [TernaryPoly.BinaryRationalHeckePrime.mem_primeIntersection_iff]
  exact mem_commSubgroup_C1 p k

theorem rc_mk_eq_iff_bin (a b : IntegralGL) :
    (Quotient.mk (QuotientGroup.rightRel (binDatum p).S) a : RC (binDatum p).S) = Quotient.mk _ b ↔
    (Quotient.mk (QuotientGroup.rightRel (TernaryPoly.OrdinaryHeckeTransfer.intersection
        TernaryPoly.BinaryRationalHeckeArithmetic.Gamma (TernaryPoly.BinaryRationalHeckePrime.primeDiagonal p)))
        (TernaryPoly.BinaryRationalHeckeArithmetic.integralEquiv a)) =
      Quotient.mk _ (TernaryPoly.BinaryRationalHeckeArithmetic.integralEquiv b) := by
  rw [rc_eq_iff, Quotient.eq (r := QuotientGroup.rightRel _), QuotientGroup.rightRel_apply, ← map_inv, ← map_mul]
  exact mem_S_iff_inter_bin p _

/-- **The paper's `p+1` binary representatives `C_c = (1 0; c p)`, `C_∞ = diag(p,1)` are a complete system of cosets `Γ₀(p) \ GL₂(ℤ)`.** -/
def primeRCEquivBin : PrimeIndex p ≃ RC (binDatum p).S :=
  Equiv.ofBijective (fun i => (Quotient.mk (QuotientGroup.rightRel (binDatum p).S) (chartLift i) : RC (binDatum p).S))
    ⟨fun i j h => TernaryPoly.BinaryRationalHeckePrime.primeCoset_injective p ((rc_mk_eq_iff_bin p _ _).mp h),
     fun q => by
      induction q using Quotient.inductionOn' with
      | h k =>
        obtain ⟨i, hi⟩ := TernaryPoly.BinaryRationalHeckePrime.primeCoset_surjective p
          (Quotient.mk _ (TernaryPoly.BinaryRationalHeckeArithmetic.integralEquiv k))
        exact ⟨i, (rc_mk_eq_iff_bin p _ _).mpr hi⟩⟩

theorem C1_chartLift (i : PrimeIndex p) :
    C1 p * binIota (chartLift i) = binIota (chartPermutation i) * (primeRepresentative p i)⁻¹ := by
  have h := TernaryPoly.BinaryRationalHeckePrime.inverse_coset_normalization p i
  have h2 := congrArg (fun x => x⁻¹) h
  simp only [mul_inv_rev, inv_inv] at h2
  rw [C1_eq_inv]
  exact h2

/-- **The chain-level Hecke operator of the binary `T₂(p)` in the paper's form.**  For every projective resolution `R` and every lift `lam`
of the correspondence, the ambient operator `ResHecke` (of which `heckeOp (binDatum p)` is the homology, `heckeOp_resolution`) is the sum over the
`p+1` representatives `C_i = primeRepresentative p i` of the paper (rows `(1 0; c p)`, `diag(p,1)`),
each acting on the coefficient by the right action `m ↦ m · C_i = ρ(C_i⁻¹) m` and on the resolution by the chain map
`Λ_i = ρ(perm_i)⁻¹ ∘ lam ∘ ρ(x_i)`. -/
theorem ResHecke_prime_paper_bin (M : Rep.{0} ℚ BinaryModularSymbol.GL2)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (binDatum p) R) (q : ℕ)
    (m : Rep.res binIota M) (r : R.complex.X q) :
    ((ResHecke (binDatum p) M R lam).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ i : PrimeIndex p, Coinvariants.mk ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ)
        (M.ρ (primeRepresentative p i)⁻¹ m ⊗ₜ[ℚ]
          (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) := by
  rw [ResHecke_f_mk]
  let T : IntegralGL → Coinvariants ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ) := fun y =>
    Coinvariants.mk ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ)
      (M.ρ (C1 p) ((Rep.res binIota M).ρ y m) ⊗ₜ[ℚ] (lam.f q).hom ((R.complex.X q).ρ y r))
  have hT : ∀ (s : (binDatum p).S) (y : IntegralGL), T ((s : IntegralGL) * y) = T y := by
    intro s y
    have hf := (binDatum p).hf s
    have e1 : M.ρ (C1 p) ((Rep.res binIota M).ρ ((s : IntegralGL) * y) m) =
        (Rep.res binIota M).ρ ((binDatum p).f s)
          (M.ρ (C1 p) ((Rep.res binIota M).ρ y m)) := by
      change M.ρ (C1 p) (M.ρ (binIota ((s : IntegralGL) * y)) m) =
        M.ρ (binIota ((binDatum p).f s)) (M.ρ (C1 p) (M.ρ (binIota y) m))
      have h : ∀ (a b : BinaryModularSymbol.GL2) (v : M), M.ρ a (M.ρ b v) = M.ρ (a * b) v := fun a b v => by
        rw [map_mul]; rfl
      have key : C1 p * binIota ((s : IntegralGL) * y) =
          binIota ((binDatum p).f s) * (C1 p * binIota y) := by
        rw [hf, map_mul]; group
      simp only [h]
      rw [key]
    have e2 : (lam.f q).hom ((R.complex.X q).ρ ((s : IntegralGL) * y) r) =
        (R.complex.X q).ρ ((binDatum p).f s) ((lam.f q).hom ((R.complex.X q).ρ y r)) := by
      rw [map_mul]
      exact Rep.hom_comm_apply (lam.f q) s _
    simp only [T]
    rw [e1, e2]
    exact Coinvariants.mk_self_apply ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ)
      ((binDatum p).f s) (M.ρ (C1 p) ((Rep.res binIota M).ρ y m) ⊗ₜ[ℚ]
        (lam.f q).hom ((R.complex.X q).ρ y r))
  have h1 : ∑ x : RC (binDatum p).S, T x.out = ∑ i : PrimeIndex p, T (chartLift i) := by
    rw [← Equiv.sum_comp (primeRCEquivBin p) (fun x : RC (binDatum p).S => T x.out)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hq : (Quotient.mk (QuotientGroup.rightRel (binDatum p).S) ((primeRCEquivBin p i).out) : RC (binDatum p).S) =
        Quotient.mk _ (chartLift i) := Quotient.out_eq _
    have hm := (rc_eq_iff (binDatum p).S _ _).mp hq
    have : chartLift i = (chartLift i * ((primeRCEquivBin p i).out)⁻¹) * (primeRCEquivBin p i).out := by group
    conv_rhs => rw [this]
    exact (hT ⟨_, hm⟩ _).symm
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [T]
  have e3 : M.ρ (C1 p) ((Rep.res binIota M).ρ (chartLift i) m) =
      (Rep.res binIota M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) := by
    change M.ρ (C1 p) (M.ρ (binIota (chartLift i)) m) =
      M.ρ (binIota (chartPermutation i)) (M.ρ (primeRepresentative p i)⁻¹ m)
    have h : ∀ (a b : BinaryModularSymbol.GL2) (v : M), M.ρ a (M.ρ b v) = M.ρ (a * b) v := fun a b v => by
      rw [map_mul]; rfl
    rw [h, h, C1_chartLift]
  rw [e3]
  have hk : ∀ b : R.complex.X q, (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹ b) = b := by
    intro b
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  have e4 : (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹
      ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) = (lam.f q).hom ((R.complex.X q).ρ (chartLift i) r) :=
    hk _
  have e5 := Coinvariants.mk_self_apply ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ)
    (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m ⊗ₜ[ℚ]
      (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r)))
  refine Eq.trans ?_ e5
  change Coinvariants.mk _ ((Rep.res binIota M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) ⊗ₜ[ℚ]
      (lam.f q).hom ((R.complex.X q).ρ (chartLift i) r)) = Coinvariants.mk _
    ((Rep.res binIota M).ρ (chartPermutation i) (M.ρ (primeRepresentative p i)⁻¹ m) ⊗ₜ[ℚ]
      (R.complex.X q).ρ (chartPermutation i) ((R.complex.X q).ρ (chartPermutation i)⁻¹
        ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))))
  rw [e4]

theorem aug_ResHecke_prime_paper_bin (M : Rep.{0} ℚ BinaryModularSymbol.GL2)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (binDatum p) R)
    (hlam : LiftOverId (binDatum p) R lam)
    (m : Rep.res binIota M) (r : R.complex.X 0) :
    augMap (Rep.res binIota M) (R.complex.X 0) (epsOf R)
        (((ResHecke (binDatum p) M R lam).f 0).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r))) =
      (epsOf R).hom r • ∑ i : PrimeIndex p, Coinvariants.mk (Rep.res binIota M).ρ
        (M.ρ (primeRepresentative p i)⁻¹ m) := by
  rw [ResHecke_prime_paper_bin, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [augMap_mk]
  congr 1
  have e1 : ∀ (g : IntegralGL) (v : R.complex.X 0), (epsOf R).hom ((R.complex.X 0).ρ g v) = (epsOf R).hom v :=
    fun g v => Rep.hom_comm_apply (epsOf R) g v
  have e2 : ∀ v : R.complex.X 0, (epsOf R).hom ((lam.f 0).hom v) = (epsOf R).hom v :=
    fun v => congrArg (fun t => t.hom v) hlam
  exact (e1 _ _).trans ((e2 _).trans (e1 _ _))

/-- `ResHecke_prime_paper_bin` with the paper's right action `m · C_i` written out. -/
theorem ResHecke_prime_paper_bin_right (M : Rep.{0} ℚ BinaryModularSymbol.GL2)
    (R : ProjectiveResolution (Rep.trivial ℚ IntegralGL ℚ)) (lam : LiftRes (binDatum p) R) (q : ℕ)
    (m : Rep.res binIota M) (r : R.complex.X q) :
    ((ResHecke (binDatum p) M R lam).f q).hom (Coinvariants.mk _ (m ⊗ₜ[ℚ] r)) =
      ∑ i : PrimeIndex p, Coinvariants.mk ((Rep.res binIota M).ρ.tprod (R.complex.X q).ρ)
        (rightAct M m (primeRepresentative p i) ⊗ₜ[ℚ]
          (R.complex.X q).ρ (chartPermutation i)⁻¹ ((lam.f q).hom ((R.complex.X q).ρ (chartLift i) r))) :=
  ResHecke_prime_paper_bin p M R lam q m r

end Binary

end TernaryPeriodPolynomials.Argument.HeckeHomology
