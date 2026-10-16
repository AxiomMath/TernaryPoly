module

public import TernaryPeriodPolynomials.SymmetricSolution.ResidueHecke.Literal.BinaryStabilityLiteral
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFinal
public import TernaryPeriodPolynomials.PeriodPolynomial.LiftableResidue.BinaryLiftableResidueDetectionActual
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod

@[expose] public section


/-!
# Lemma 4.5 on literal homology: the eigenperiod argument and the residue removal

Formalized by Claude Sonnet 5.5.  Paper: Lemma 4.5, its proof, the eigenperiod argument and the pole removal.

On top of the `Lemma45Literal` (`LnHom`, `LnHom_binary_stable_literal`, `LnHom_extreme_literal`), the unconditional Hecke bridge
`homologyHomBridge_holds : T₂(p) = p^{d+1} · periodHecke d diag(p,1)`, and the library eigenperiod detection:
* `LnQ`, `LnC`: `𝓛_n` in rational period coordinates and its complexification `𝓛_n ⊗_ℚ ℂ ⊆ space ℂ (n+1)`;
* `LnQ_stable`, `LnC_stable`: stability under the literal homology `T₂(p)` and, through the bridge, under the analytic prime operator
  `complexHecke (n+1) diag(p,1)` (the operator whose eigenperiods are the `oddPeriod h`, `periodMap_hecke`);
* `LnC_extreme`: `[X Y^{d-1}] q = 0` on `𝓛_n ⊗ ℂ`;
* `LnC_eq_bot` (odd `n`): a nonzero stable subspace killed by the extreme coefficient does not exist, because every common eigenperiod `q_h`
  has `[X Y^{d-1}] q_h = -d i^d Γ(d)(2π)^{-d} L(h,d) ≠ 0` (`BinaryCuspPeriodDetection.actual_stable_extreme_kernel_eq_bot`, Lemma 2.5);
* `LnHom_eq_bot`: `𝓛_n = 0` on literal homology for every `n` (even `n`: the period space of odd degree `n + 1` is zero, `periodSpace_odd_eq_bot`);
* `residue_of_top_class_zero`, `top_cycle_literal_residue_zero`: the residue of every class of `H₃(G, ℳ_n ⊗ det)` vanishes; in particular
  the literal residue along `a = 0` of the trace cycle `S = ∑ F(r)` vanishes (`res_{a=0} S = 2 q_0 = 0`);
* `liftableResidueHoms_eq_bot_of_homology`: the Hom-model liftable residues vanish, derived from literal homology.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Lemma45Full

open TernaryPoly TernaryPoly.BinaryComplexPeriod TernaryPoly.OrdinaryResiduePeriod
open TernaryPeriodPolynomials.Argument.Lemma45Literal
open TernaryPeriodPolynomials.Argument.HeckeNormalization

/-- `𝓛_n` in rational period coordinates `space ℚ (n+1)`. -/
def LnQ (n : ℕ) : Submodule ℚ (space ℚ (n + 1)) := (LnHom n).map (rationalEquiv (n + 1)).toLinearMap

/-- The complexification `𝓛_n ⊗_ℚ ℂ ⊆ space ℂ (n+1)` (the actual complex span of the rational coefficient extension). -/
def LnC (n : ℕ) : Submodule ℂ (space ℂ (n + 1)) := complexSpan (n + 1) (LnQ n)

/-- Literal-homology stability of `𝓛_n` under `T₂(p)` in rational period coordinates. -/
theorem LnQ_stable (p n : ℕ) [Fact p.Prime] (q : space ℚ (n + 1)) (hq : q ∈ LnQ n) :
    homologyRationalT2 p (n + 1) q ∈ LnQ n := by
  obtain ⟨q', hq', rfl⟩ := hq
  refine ⟨T2B p n q', LnHom_binary_stable_literal p n q' hq', ?_⟩
  rfl

/-- **`𝓛_n ⊗ ℂ` is stable under the analytic prime operator** `complexHecke (n+1) diag(p,1)`, via the literal homology operator
`T₂(p)` and the unconditional bridge `T₂(p) = p^{d+1} · periodHecke`. -/
theorem LnC_stable (p n : ℕ) [Fact p.Prime] (q : space ℂ (n + 1)) (hq : q ∈ LnC n) :
    complexHecke (n + 1) (BinaryRationalHeckePrime.primeDiagonal p) q ∈ LnC n := by
  have h1 : homologyComplexT2 p (n + 1) q ∈ LnC n :=
    complexSpan_stable (n + 1) (LnQ n) (homologyRationalT2 p (n + 1)) (homologyComplexT2 p (n + 1))
      (fun q hq => LnQ_stable p n q hq) (fun q => complexifyEnd_extend (n + 1) _ q) q hq
  rw [homologyComplexT2_of_bridge (homologyHomBridge_holds p (n + 1))] at h1
  have hp : (((p : ℚ) ^ (n + 1 + 1) : ℚ) : ℂ) ≠ 0 := by
    have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    exact_mod_cast pow_ne_zero _ this
  have h2 := (LnC n).smul_mem ((((p : ℚ) ^ (n + 1 + 1) : ℚ) : ℂ)⁻¹) h1
  rw [LinearMap.smul_apply, smul_smul, inv_mul_cancel₀ hp, one_smul] at h2
  exact h2

/-- The extreme coefficient `[a c^n] q` vanishes on `𝓛_n ⊗ ℂ`. -/
theorem LnC_extreme (n : ℕ) : ∀ q ∈ LnC n, extreme ℂ (n + 1) q = 0 := by
  apply complexSpan_extreme
  rintro _ ⟨q', hq', rfl⟩
  have h := LnHom_extreme_literal n q' hq'
  change q'.val.val.coeff (Finsupp.single 0 1 + Finsupp.single 1 (n + 1 - 1)) = 0
  rw [Nat.add_sub_cancel]
  exact h

open MvPolynomial in
theorem prod_supp_eq_univ {R : Type*} [CommMonoid R] (g : Fin 2 → R) (m : Fin 2 →₀ ℕ) :
    ∏ i ∈ m.support, g i ^ m i = ∏ i, g i ^ m i :=
  Finset.prod_subset (Finset.subset_univ _) (fun i _ hi => by simp [Finsupp.notMem_support_iff.mp hi])

open MvPolynomial in
/-- Substituting `(x, y) ↦ (-x, -y)` multiplies a homogeneous polynomial of degree `d` by `(-1)^d`. -/
theorem bind_neg_homog (q : MvPolynomial (Fin 2) ℚ) (d : ℕ) (h : q.IsHomogeneous d) :
    bind₁ (![-X 0, -X 1] : Fin 2 → MvPolynomial (Fin 2) ℚ) q = (-1 : ℚ) ^ d • q := by
  conv_lhs => rw [q.as_sum]
  conv_rhs => rw [q.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : m 0 + m 1 = d := by
    have := h (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  rw [bind₁_monomial, smul_monomial, monomial_eq, Finsupp.prod, prod_supp_eq_univ, prod_supp_eq_univ]
  rw [Fin.prod_univ_two, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [neg_pow (X 0 : MvPolynomial (Fin 2) ℚ), neg_pow (X 1 : MvPolynomial (Fin 2) ℚ)]
  have : ((-1 : ℚ) ^ d) = (-1) ^ (m 0) * (-1) ^ (m 1) := by rw [← pow_add, hmd]
  rw [this]
  simp [map_mul, map_pow]
  ring

/-- In odd degree the period space is zero: a symmetric, separately odd form of odd degree is even and odd at once. -/
theorem periodSpace_odd_eq_bot (d : ℕ) (hd : Odd d) : periodSpace d = ⊥ := by
  apply eq_bot_iff.mpr
  intro q hq
  have h := (mem_periodSpace d q).mp hq
  have hs : TernaryPeriodPolynomials.Argument.FareyTree.Sym3 q.val := ⟨h.swap, h.odd_first, h.odd_second⟩
  have he := hs.even
  have hh : q.val.IsHomogeneous d := by
    have := q.2
    rwa [MvPolynomial.mem_homogeneousSubmodule] at this
  rw [bind_neg_homog q.val d hh, hd.neg_one_pow, neg_one_smul] at he
  apply (Submodule.mem_bot ℚ).mpr
  apply Subtype.ext
  have h2 : (2 : ℚ) • q.val = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← he]
    simp
  have := (smul_eq_zero.mp h2).resolve_left (by norm_num)
  simpa using this

open TernaryPoly.BinaryLiftableResidueDetection in
/-- **The eigenperiod argument**, from literal homology: for odd `n`, the complexification of `𝓛_n` is stable under the
usual prime operators (`LnC_stable`, via the literal homology `T₂(p)` and `HomologyHomBridge`) and killed by the extreme coefficient
(`LnC_extreme`), so by the nonvanishing of the extreme coefficient of every common eigenperiod (`BinaryCuspPeriod.coeff_oddPeriod_extreme`,
`moment_nat_eq` and Lemma 2.5, inside `actual_stable_extreme_kernel_eq_bot`) it is zero. -/
theorem LnC_eq_bot (n : ℕ) (hn : Odd n) : LnC n = ⊥ := by
  apply BinaryCuspPeriodDetection.actual_stable_extreme_kernel_eq_bot (n + 1) (successor_even hn)
    (actualIntertwining (n + 1) (successor_even hn)) (LnC n)
  · intro p q hq
    have : Fact p.val.Prime := ⟨(Nat.irreducible_iff_nat_prime _).mp p.property⟩
    exact LnC_stable p.val n q hq
  · exact LnC_extreme n

/-- **`𝓛_n = 0` on literal homology**, for every `n` (odd `n` by the eigenperiod argument, even `n` since the period space of odd
degree `n + 1` is zero). -/
theorem LnHom_eq_bot (n : ℕ) : LnHom n = ⊥ := by
  rcases Nat.even_or_odd n with he | ho
  · apply eq_bot_iff.mpr
    intro q _
    have : periodSpace (n + 1) = ⊥ := periodSpace_odd_eq_bot (n + 1) he.add_one
    have h0 : q.val = 0 := (Submodule.mem_bot ℚ).mp (this ▸ q.2)
    exact (Submodule.mem_bot ℚ).mpr (Subtype.ext h0)
  · have h1 : LnQ n = ⊥ := (complexSpan_eq_bot_iff (n + 1) (LnQ n)).mp (LnC_eq_bot n ho)
    apply eq_bot_iff.mpr
    intro q hq
    have : rationalEquiv (n + 1) q ∈ LnQ n := ⟨q, hq, rfl⟩
    rw [h1, Submodule.mem_bot] at this
    exact (Submodule.mem_bot ℚ).mpr ((rationalEquiv (n + 1)).injective (by simpa using this))

section Residue

open TernaryPeriodPolynomials.Argument.AppendixBResidue TernaryPeriodPolynomials.Argument.HeckeHomology TernaryPoly.ModThreeGoodAction
  TernaryPoly.SinglePoleCoordinate

/-- The map `H₃(G, ℳ_n ⊗ det) → H₃(G, ℛ_n ⊗ det)` induced by the residue. -/
def resImage (n : ℕ) : groupHomology (MRep n) 3 →ₗ[ℚ] groupHomology (ResRep n) 3 :=
  (groupHomology.map (MonoidHom.id TernaryPoly.ModThreeGoodAction.IntegralGL) (residueRepG n) 3).hom

/-- **Every class of `H₃(G, ℳ_n ⊗ det)` has vanishing literal residue** (the image of `H₃(G, ℳ_n)` in `ℬ_{n+1}` is zero). -/
theorem residue_of_top_class_zero (n : ℕ) (x : groupHomology (MRep n) 3) :
    resHLit n (resImage n x) = 0 := by
  have h : resHLit n (resImage n x) ∈ LnHom n :=
    ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [LnHom_eq_bot] at h
  exact (Submodule.mem_bot ℚ).mp h

/-- **The literal pole removal**: for every full-group top cycle `S` with coefficients in `ℳ_n ⊗ det` (a
`G`-equivariant functional on the Steinberg module with values in the single-pole functions), the literal residue along `a = 0`
of its image in `ℛ_n`, at the identity apartment, vanishes. -/
theorem top_cycle_literal_residue_zero (n : ℕ) (S : OrdinaryFullCoefficient.SinglePoleHom n (-1)) :
    literalFiberMap n 0
      (((OrdinaryFullCoefficient.residueHom n (-1) S).val (OrdinaryApartmentPresentation.frameCycle 1))
        (OrdinaryResidueSupport.axis 0)) = 0 := by
  set x := (H3_G_equiv_M n).symm S with hx
  have h1 := residue_of_top_class_zero n x
  have h2 := residue_at_a_eq_zero n (resImage n x)
  rw [h1] at h2
  have h3 := H3_G_equiv_natural n x
  change H3_G_equiv n (resImage n x) = _ at h3
  rw [h3, hx, LinearEquiv.apply_symm_apply] at h2
  exact h2.symm

/-- **The Hom-model liftable residues vanish**, derived from literal homology: `liftableResidueHoms n (-1) = 0` for every `n`. -/
theorem liftableResidueHoms_eq_bot_of_homology (n : ℕ) :
    OrdinaryFullCoefficient.liftableResidueHoms n (-1) = ⊥ := by
  apply eq_bot_iff.mpr
  intro Φ hΦ
  have h : OrdinaryResiduePeriod.periodEquiv n Φ ∈ LnHom n := by
    rw [LnHom_eq_liftable]; exact ⟨Φ, hΦ, rfl⟩
  rw [LnHom_eq_bot, Submodule.mem_bot] at h
  exact (Submodule.mem_bot ℚ).mpr ((OrdinaryResiduePeriod.periodEquiv n).injective
    (h.trans (LinearEquiv.map_zero (OrdinaryResiduePeriod.periodEquiv n)).symm))

end Residue

end TernaryPeriodPolynomials.Argument.Lemma45Full
