module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.ParabolicDuality.Parabolic
public import TernaryPeriodPolynomials.PeriodPolynomial.FareyDuality.FarePeriod
public import TernaryPeriodPolynomials.ArithmeticCohomology.HeckeNormalization.BridgeFrobeniusL2

@[expose] public section


/-!
# The principal congruence subgroups `Γ(N)`, `N ≥ 3`, as Farey data

Formalized by Claude Sonnet 5.5.  Paper: `ar:eq:facepair`.

* `gammaNGL N`: the kernel of `GL₂(ℤ) → GL₂(ℤ/N)`;
* `gammaN_freeT`: for `N ≥ 3`, `Γ(N)` acts freely on the Farey triangles (a triangle stabiliser has entries in `{-1,0,1}`, and an element
  of `Γ(N)` with such entries is trivial); `gammaN_noFlip`: no element of `Γ(N)` reverses an oriented dual edge;
* `gammaN_finiteOrbits`: `Γ(N)` has finite index, so finitely many orbits of triangles; `repSystemOfFinite` turns this into a system of
  orbit representatives;
* `gammaNFareyData`: the resulting `FareyData`;
* `dualCoupling ρ`: the perfect invariant pairing between a finite-dimensional representation `E` and its dual.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNParabolicPD

open TernaryPeriodPolynomials.Argument.FareyTree TernaryPoly.RankTwoAugmentedFrames
open scoped Classical

/-- The principal congruence subgroup `Γ(N) = ker (GL₂(ℤ) → GL₂(ℤ/N))`; for `N ≥ 3` it is contained in `SL₂(ℤ)`. -/
def gammaNGL (N : ℕ) : Subgroup IntegralGL :=
  (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) : IntegralGL →* GL (Fin 2) (ZMod N)).ker

theorem mem_gammaNGL {N : ℕ} {g : IntegralGL} :
    g ∈ gammaNGL N ↔ ((g.val 0 0 : ℤ) : ZMod N) = 1 ∧ ((g.val 0 1 : ℤ) : ZMod N) = 0 ∧
      ((g.val 1 0 : ℤ) : ZMod N) = 0 ∧ ((g.val 1 1 : ℤ) : ZMod N) = 1 := by
  unfold gammaNGL
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have h' := congrArg (fun m : GL (Fin 2) (ZMod N) => (m : Matrix (Fin 2) (Fin 2) (ZMod N))) h
    have e00 := congrFun (congrFun h' 0) 0
    have e01 := congrFun (congrFun h' 0) 1
    have e10 := congrFun (congrFun h' 1) 0
    have e11 := congrFun (congrFun h' 1) 1
    simp [Matrix.GeneralLinearGroup.map] at e00 e01 e10 e11
    exact ⟨e00, e01, e10, e11⟩
  · rintro ⟨a, b, c, d⟩
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map, a, b, c, d]

/-- A matrix of `Γ(N)` (`N ≥ 3`) with entries in `{-1, 0, 1}` is the identity. -/
theorem gammaN_small {N : ℕ} (hN : 3 ≤ N) {g : IntegralGL} (hg : g ∈ gammaNGL N)
    (h : ∀ i j, |g.val i j| ≤ 1) : g = 1 := by
  rw [mem_gammaNGL] at hg
  obtain ⟨a, b, c, d⟩ := hg
  have h3 : (3 : ℤ) ≤ N := by exact_mod_cast hN
  have key : ∀ x : ℤ, |x| ≤ 2 → ((x : ℤ) : ZMod N) = 0 → x = 0 := by
    intro x hx hx0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hx0
    exact Int.eq_zero_of_abs_lt_dvd hx0 (lt_of_le_of_lt hx (by omega))
  have small : ∀ i j, |g.val i j| ≤ 2 := fun i j => (h i j).trans (by norm_num)
  have dif : ∀ x : ℤ, |x| ≤ 1 → |x - 1| ≤ 2 := fun x hx => by
    rw [abs_le] at hx ⊢; constructor <;> linarith [hx.1, hx.2]
  have e00 : g.val 0 0 - 1 = 0 := key _ (dif _ (h 0 0)) (by push_cast; rw [a]; simp)
  have e11 : g.val 1 1 - 1 = 0 := key _ (dif _ (h 1 1)) (by push_cast; rw [d]; simp)
  have e01 : g.val 0 1 = 0 := key _ (small 0 1) b
  have e10 : g.val 1 0 = 0 := key _ (small 1 0) c
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> omega

theorem entPlus_abs {a b c d : ℤ} (h : EntPlus a b c d) : |a| ≤ 1 ∧ |b| ≤ 1 ∧ |c| ≤ 1 ∧ |d| ≤ 1 := by
  unfold EntPlus at h
  rcases h with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ |
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ |
    ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩ <;> simp [ha, hb, hc, hd]

theorem stab_triPlus_small {N : ℕ} (hN : 3 ≤ N) {g : IntegralGL} (hg : g ∈ gammaNGL N)
    (hs : g ∈ MulAction.stabilizer IntegralGL triPlus) : g = 1 := by
  have h := entPlus_abs (stab_entries g hs)
  refine gammaN_small hN hg ?_
  intro i j
  fin_cases i <;> fin_cases j
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

/-- `Γ(N)`, `N ≥ 3`, acts freely on the Farey triangles. -/
theorem gammaN_freeT {N : ℕ} (hN : 3 ≤ N) : FreeAction (gammaNGL N) Tri := by
  intro γ t h
  obtain ⟨g, rfl⟩ := exists_smul_triPlus t
  have hγ : (γ : IntegralGL) ∈ gammaNGL N := γ.2
  have hconj : g⁻¹ * (γ : IntegralGL) * g ∈ gammaNGL N := by
    have := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) :
      IntegralGL →* GL (Fin 2) (ZMod N))).conj_mem _ hγ g⁻¹
    simpa [gammaNGL] using this
  have hst : g⁻¹ * (γ : IntegralGL) * g ∈ MulAction.stabilizer IntegralGL triPlus := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul]
    have h' : (γ : IntegralGL) • g • triPlus = g • triPlus := h
    rw [h', inv_smul_smul]
  have h1 := stab_triPlus_small hN hconj hst
  have h2 : (γ : IntegralGL) = 1 := by
    have : (γ : IntegralGL) = g * (g⁻¹ * (γ : IntegralGL) * g) * g⁻¹ := by group
    rw [this, h1]; group
  exact Subtype.ext h2

theorem sOne_entries : sOne.val 0 0 = 1 ∧ sOne.val 0 1 = 0 ∧ sOne.val 1 0 = 0 ∧ sOne.val 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [sOne, colGL_val_zero, colGL_val_one, e1, e2]

/-- No element of `Γ(N)`, `N ≥ 3`, reverses an oriented dual edge. -/
theorem gammaN_noFlip {N : ℕ} (hN : 3 ≤ N) : ∀ (γ : gammaNGL N) (q : OTE), γ • q ≠ q.swap := by
  intro γ q h
  obtain ⟨g, rfl⟩ := ote_transitive q
  have hγ : (γ : IntegralGL) ∈ gammaNGL N := γ.2
  have hconj : g⁻¹ * (γ : IntegralGL) * g ∈ gammaNGL N := by
    have := (MonoidHom.normal_ker (Matrix.GeneralLinearGroup.map (Int.castRingHom (ZMod N)) :
      IntegralGL →* GL (Fin 2) (ZMod N))).conj_mem _ hγ g⁻¹
    simpa [gammaNGL] using this
  set γ' := g⁻¹ * (γ : IntegralGL) * g with hγ'
  have hp : γ' • p0 = p0.swap := by
    have h1 : (γ : IntegralGL) • g • p0 = (g • p0).swap := h
    rw [hγ', mul_smul, mul_smul, h1, ← OTE.swap_smul, inv_smul_smul]
  have ht : γ' • triPlus = triMinus := by
    have := congrArg (fun p : OTE => p.1.1) hp
    exact this
  have hst : (sOne⁻¹ * γ') ∈ MulAction.stabilizer IntegralGL triPlus := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ht, sOne_inv, sOne_smul_triMinus]
  have hent := entPlus_abs (stab_entries _ hst)
  have hγ'eq : γ' = sOne * (sOne⁻¹ * γ') := by group
  have hsmall : ∀ i j, |γ'.val i j| ≤ 1 := by
    obtain ⟨s00, s01, s10, s11⟩ := sOne_entries
    have hv : γ'.val = sOne.val * (sOne⁻¹ * γ').val := by
      conv_lhs => rw [hγ'eq]
      rw [Units.val_mul]
    obtain ⟨e00, e01, e10, e11⟩ := hent
    generalize (sOne⁻¹ * γ' : IntegralGL).val = m at hv e00 e01 e10 e11
    intro i j
    rw [hv, Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [s00, s01, s10, s11] <;> assumption
  have h1 := gammaN_small hN hconj hsmall
  rw [h1, one_smul] at ht
  exact triPlus_ne_triMinus ht

/-- A finite number of orbits yields a finite system of orbit representatives. -/
def repSystemOfFinite {Γ X : Type} [Group Γ] [MulAction Γ X]
    (hfin : Finite (MulAction.orbitRel.Quotient Γ X)) : RepSystem Γ X :=
  haveI := Fintype.ofFinite (MulAction.orbitRel.Quotient Γ X)
  { R := Finset.univ.image (fun q : MulAction.orbitRel.Quotient Γ X => q.out)
    cover := by
      intro x
      refine ⟨(Quotient.mk (MulAction.orbitRel Γ X) x).out, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
      have h : (MulAction.orbitRel Γ X) (Quotient.mk (MulAction.orbitRel Γ X) x).out x :=
        Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ X) x))
      rw [MulAction.orbitRel_apply] at h
      obtain ⟨γ, hγ⟩ := h
      refine ⟨γ⁻¹, ?_⟩
      rw [← hγ]
      exact inv_smul_smul γ x
    inj := by
      intro r hr r' hr' γ h
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hr'
      have h1 : Quotient.mk (MulAction.orbitRel Γ X) q.out = Quotient.mk (MulAction.orbitRel Γ X) q'.out := by
        refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
        exact ⟨γ⁻¹, by show γ⁻¹ • Quotient.out q' = Quotient.out q; rw [← h, inv_smul_smul]⟩
      rw [Quotient.out_eq, Quotient.out_eq] at h1
      rw [h1] }

theorem gammaN_finiteIndex {N : ℕ} (hN : 3 ≤ N) : (gammaNGL N).FiniteIndex := by
  have : NeZero N := ⟨by omega⟩
  unfold gammaNGL
  exact Subgroup.finiteIndex_ker _

theorem gammaN_finiteOrbits {N : ℕ} (hN : 3 ≤ N) : Finite (MulAction.orbitRel.Quotient (gammaNGL N) Tri) := by
  have := gammaN_finiteIndex hN
  have : (gammaNGL N).subtype.range.FiniteIndex := by
    rw [Subgroup.range_subtype]; exact gammaN_finiteIndex hN
  obtain ⟨I, hI, hcov⟩ := TernaryPeriodPolynomials.Argument.HeckeNormalization.exists_finite_orbit_reps
    (X := Tri) (gammaNGL N).subtype tri_htr
  have := hI.to_subtype
  refine Finite.of_surjective (fun i : I => (Quotient.mk (MulAction.orbitRel (gammaNGL N) Tri) i.1)) ?_
  intro q
  induction q using Quotient.inductionOn with
  | h x =>
    obtain ⟨i, hi, σ, hσ⟩ := hcov x
    refine ⟨⟨i, hi⟩, ?_⟩
    refine Quotient.sound (MulAction.orbitRel_apply.mpr ?_)
    exact ⟨σ⁻¹, by rw [hσ]; change ((σ⁻¹ : gammaNGL N) : IntegralGL) • ((σ : IntegralGL) • i) = i; simp⟩

/-- The Farey data of `Γ(N)`, `N ≥ 3`. -/
def gammaNFareyData {N : ℕ} (hN : 3 ≤ N) : FareyData (gammaNGL N) where
  RT := repSystemOfFinite (gammaN_finiteOrbits hN)
  freeT := gammaN_freeT hN
  noFlip := gammaN_noFlip hN

section Dual

variable {Γ : Subgroup IntegralGL} {E : Type} [AddCommGroup E] [Module ℂ E]

/-- The perfect invariant pairing between a finite-dimensional representation and its dual. -/
def dualCoupling [FiniteDimensional ℂ E] (ρ : Representation ℂ Γ E) : Coupling ρ ρ.dual where
  e := Module.Dual.eval ℂ E
  inv := fun γ v φ => by
    simp only [Representation.dual_apply, Module.Dual.eval_apply, Module.Dual.transpose_apply, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  left := fun v hv => (Module.forall_dual_apply_eq_zero_iff ℂ v).mp hv
  right := fun φ hφ => by
    ext v
    simpa using hφ v

end Dual

end TernaryPeriodPolynomials.Argument.GammaNParabolicPD
