module

public import TernaryPeriodPolynomials.ModularForm.EichlerShimura.CentralSign

@[expose] public section


/-!
# Eichler–Shimura spanning at level two via the index-two subgroup `Γ'(2)`

`Γ(2)` contains `-1`, which acts on `Sym^{n+1} ⊗ det⁻¹` by `(-1)^{n+1}`. For even `n` the spanning
statement is trivial (`CentralSign.esSpan_of_neg_one_mem_of_even`). For odd `n` this file reduces it
to the index-two subgroup `Γ'(2) = {g ∈ Γ(2) | g₀₀ ≡ 1 (mod 4)}`, which does not contain `-1`
(`neg_one_not_mem_gammaTwoPrime`) and has finite index (`Γ(4) ≤ Γ'(2)`):

* cusp forms of even weight for `Γ'(2)` are cusp forms for `Γ(2)` (`liftCusp`, using
  `slash_neg_even` and `isCusp_lift`);
* their holomorphic and antiholomorphic period cocycles restrict correctly (`resLin_holCocycle`,
  `resLin_antiholCocycle`, from uniqueness of the normalized moment primitives `prim_unique`);
* a cocycle of `Γ(2)` that is a coboundary on `Γ'(2)` is a coboundary, since `-1` acts trivially
  (`coboundary_of_res`);

so `ESSpan Γ'(2) n → ESSpan Γ(2) n` (`esSpan_gamma2_of_prime`).

Written by Claude Opus 5.5.
-/

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups

namespace TernaryPeriodPolynomials.Argument.ESFoundations.LevelTwo

/-- `Γ'(2)`: the elements of `Γ(2)` with upper-left entry `≡ 1 (mod 4)`. -/
def gammaTwoPrime : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ Gamma 2 ∧ ((g 0 0 : ℤ) : ZMod 4) = 1}
  one_mem' := ⟨(Gamma 2).one_mem, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha4⟩ ⟨hb, hb4⟩
    refine ⟨(Gamma 2).mul_mem ha hb, ?_⟩
    rw [Gamma_mem] at ha hb
    have h01 : (2 : ℤ) ∣ a 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast ha.2.1)
    have h10 : (2 : ℤ) ∣ b 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast hb.2.2.1)
    have e : ((a * b : SL(2, ℤ)) 0 0 : ℤ) = a 0 0 * b 0 0 + a 0 1 * b 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    obtain ⟨s, hs⟩ := h01
    obtain ⟨t, ht⟩ := h10
    rw [hs, ht]
    push_cast
    rw [ha4, hb4]
    ring_nf
    rw [show (4 : ZMod 4) = 0 from rfl]
    ring
  inv_mem' := by
    rintro a ⟨ha, ha4⟩
    refine ⟨(Gamma 2).inv_mem ha, ?_⟩
    rw [Gamma_mem] at ha
    have hdet := a.2
    rw [Matrix.det_fin_two] at hdet
    have h01 : (2 : ℤ) ∣ a 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast ha.2.1)
    have h10 : (2 : ℤ) ∣ a 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast ha.2.2.1)
    have e : ((a⁻¹ : SL(2, ℤ)) 0 0 : ℤ) = a 1 1 := by
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    rw [e]
    obtain ⟨s, hs⟩ := h01
    obtain ⟨t, ht⟩ := h10
    have : ((a 0 0 * a 1 1 : ℤ) : ZMod 4) = 1 := by
      have h' : a 0 0 * a 1 1 = 1 + (2 * s) * (2 * t) := by rw [← hs, ← ht]; linarith
      rw [h']; push_cast; ring_nf; rw [show (4 : ZMod 4) = 0 from rfl]; ring
    push_cast at this
    rw [ha4, one_mul] at this
    exact this


theorem gammaTwoPrime_le : gammaTwoPrime ≤ Gamma 2 := fun _ h => h.1

private theorem cast_one_of_dvd {N : ℕ} {x : ℤ} (h : (N : ℤ) ∣ x - 1) : (x : ZMod N) = 1 := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - 1) N).mpr h
  push_cast at this
  exact sub_eq_zero.mp this

private theorem dvd_sub_one {N : ℕ} {x : ℤ} (h : (x : ZMod N) = 1) : (N : ℤ) ∣ x - 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h, sub_self]

private theorem dvd2_of_gamma2 {g : SL(2, ℤ)} (h : g ∈ Gamma 2) :
    (2 : ℤ) ∣ g 0 1 ∧ (2 : ℤ) ∣ g 1 0 ∧ (2 : ℤ) ∣ g 0 0 - 1 ∧ (2 : ℤ) ∣ g 1 1 - 1 := by
  rw [Gamma_mem] at h
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast h.2.1),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp (by exact_mod_cast h.2.2.1), ?_, ?_⟩
  · exact_mod_cast dvd_sub_one (N := 2) (by exact_mod_cast h.1)
  · exact_mod_cast dvd_sub_one (N := 2) (by exact_mod_cast h.2.2.2)

theorem neg_one_not_mem_gammaTwoPrime : (-1 : SL(2, ℤ)) ∉ gammaTwoPrime := by
  rintro ⟨-, h⟩
  have : ((-1 : ℤ) : ZMod 4) = 1 := by simpa using h
  revert this; decide

theorem mem_or_neg_mem {g : SL(2, ℤ)} (h : g ∈ Gamma 2) :
    g ∈ gammaTwoPrime ∨ -g ∈ gammaTwoPrime := by
  obtain ⟨-, -, ⟨s, hs⟩, -⟩ := dvd2_of_gamma2 h
  have hg : g 0 0 = 1 + 2 * s := by linarith
  have hneg : -g ∈ Gamma 2 := by
    have : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
      rw [Gamma_mem]; simp
    simpa using (Gamma 2).mul_mem this h
  rcases Int.even_or_odd s with ⟨t, ht⟩ | ⟨t, ht⟩
  · left; refine ⟨h, ?_⟩; rw [hg, ht]; push_cast; ring_nf
    rw [show (4 : ZMod 4) = 0 from rfl]; ring
  · right; refine ⟨hneg, ?_⟩
    have e : ((-g : SL(2, ℤ)) 0 0 : ℤ) = -g 0 0 := by simp
    rw [e, hg, ht]; push_cast; ring_nf
    rw [show (4 : ZMod 4) = 0 from rfl]; ring_nf; decide

theorem Gamma4_le_gammaTwoPrime : Gamma 4 ≤ gammaTwoPrime := by
  intro g hg
  rw [Gamma_mem] at hg
  obtain ⟨h00, h01, h10, h11⟩ := hg
  have d00 := dvd_sub_one (N := 4) h00
  have d11 := dvd_sub_one (N := 4) h11
  have d01 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h01
  have d10 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp h10
  have two4 : (2 : ℤ) ∣ 4 := ⟨2, by norm_num⟩
  refine ⟨?_, h00⟩
  rw [Gamma_mem]
  refine ⟨cast_one_of_dvd (N := 2) (two4.trans (by exact_mod_cast d00)),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (two4.trans (by exact_mod_cast d01)),
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mpr (two4.trans (by exact_mod_cast d10)),
    cast_one_of_dvd (N := 2) (two4.trans (by exact_mod_cast d11))⟩

instance : gammaTwoPrime.FiniteIndex := Subgroup.finiteIndex_of_le Gamma4_le_gammaTwoPrime

theorem mul_self_mem {g : SL(2, ℤ)} (h : g ∈ Gamma 2) : g * g ∈ gammaTwoPrime := by
  rcases mem_or_neg_mem h with h' | h'
  · exact gammaTwoPrime.mul_mem h' h'
  · have := gammaTwoPrime.mul_mem h' h'
    simpa using this


open UpperHalfPlane ModularForm TernaryPeriodPolynomials.Argument.SeedC3S4c

theorem slash_neg_even (k : ℤ) (hk : Even k) (f : ℍ → ℂ) (γ : GL (Fin 2) ℝ) :
    f ∣[k] (-γ) = f ∣[k] γ := by
  funext τ
  rw [slash_apply, slash_apply, UpperHalfPlane.neg_smul]
  have hdet : (-γ).det = γ.det := by
    ext; simp [Matrix.det_neg]
  have hσ : σ (-γ) = σ γ := by simp [σ, hdet]
  have hden : denom (-γ) τ = -denom γ τ := by
    simp [denom]; ring
  rw [hσ, hdet, hden]
  congr 1
  rw [show -denom γ τ = (-1) * denom γ τ by ring, mul_zpow, (hk.neg).neg_one_zpow, one_mul]

theorem mapGL_neg (g : SL(2, ℤ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ (-g) = -Matrix.SpecialLinearGroup.mapGL ℝ g := by
  ext i j; simp [Matrix.SpecialLinearGroup.mapGL]

theorem isCusp_lift {c : OnePoint ℝ} (hc : IsCusp c (LamGL (Gamma 2))) :
    IsCusp c (LamGL gammaTwoPrime) := by
  obtain ⟨γ, hγ, hpar, hfix⟩ := hc
  obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
  refine ⟨Matrix.SpecialLinearGroup.mapGL ℝ (g * g),
    Subgroup.mem_map_of_mem _ (mul_self_mem hg), ?_, ?_⟩
  · rw [map_mul, ← sq]; exact hpar.pow two_ne_zero
  · rw [map_mul, mul_smul, hfix, hfix]

/-- A cusp form for `Γ'(2)` of even weight is a cusp form for `Γ(2)`. -/
def liftCusp {k : ℤ} (hk : Even k) (f : CuspForm (LamGL gammaTwoPrime) k) :
    CuspForm (LamGL (Gamma 2)) k where
  toFun := f
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    rcases mem_or_neg_mem hg with h | h
    · exact f.slash_action_eq' _ (Subgroup.mem_map_of_mem _ h)
    · have := f.slash_action_eq' _ (Subgroup.mem_map_of_mem _ h)
      rwa [mapGL_neg, slash_neg_even k hk] at this
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (isCusp_lift hc)

theorem liftCusp_apply {k : ℤ} (hk : Even k) (f : CuspForm (LamGL gammaTwoPrime) k) (τ : ℍ) :
    liftCusp hk f τ = f τ := rfl


open MvPolynomial CategoryTheory groupCohomology
open TernaryPeriodPolynomials.Argument.SeedC3S4c
open TernaryPeriodPolynomials.Argument.SeedC3

theorem prim_unique {G G' h : ℂ → ℂ} (hG : ∀ z : ℂ, 0 < z.im → HasDerivAt G (h z) z)
    (hG' : ∀ z : ℂ, 0 < z.im → HasDerivAt G' (h z) z) (h0 : G Complex.I = 0)
    (h0' : G' Complex.I = 0) {z : ℂ} (hz : 0 < z.im) : G z = G' z := by
  set s : Set ℂ := {z | 0 < z.im}
  have hs : IsOpen s := isOpen_lt continuous_const Complex.continuous_im
  have hc : IsPreconnected s := (convex_halfSpace_im_gt 0).isPreconnected
  have hd : ∀ w ∈ s, HasDerivAt (G - G') 0 w := fun w hw => by
    have := (hG w hw).sub (hG' w hw)
    rwa [sub_self] at this
  have hdiff : DifferentiableOn ℂ (G - G') s :=
    fun w hw => (hd w hw).differentiableAt.differentiableWithinAt
  have hderiv : s.EqOn (deriv (G - G')) 0 := fun w hw => (hd w hw).deriv
  have hI : Complex.I ∈ s := by show 0 < Complex.I.im; simp
  have := hs.is_const_of_deriv_eq_zero hc hdiff hderiv hz hI
  simp only [Pi.sub_apply, h0, h0', sub_zero] at this
  exact sub_eq_zero.mp this

variable {n : ℕ}

theorem even_weight (hn : Odd n) : Even (((n + 3 : ℕ) : ℤ)) := by
  obtain ⟨t, rfl⟩ := hn
  exact ⟨(t + 2 : ℤ), by push_cast; ring⟩

theorem eichlerForm_liftCusp (hn : Odd n)
    (f : CuspForm (LamGL gammaTwoPrime) ((n + 3 : ℕ) : ℤ)) (m : SL(2, ℤ)) :
    (eichlerForm (Λ := Gamma 2) (liftCusp (even_weight hn) f) m).1 =
      (eichlerForm (Λ := gammaTwoPrime) f m).1 := by
  change eichlerCocycle n _ _ = eichlerCocycle n _ _
  unfold eichlerCocycle eichlerPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  have hw : 0 < (mob (Matrix.SpecialLinearGroup.mapGL ℝ m) Complex.I).im :=
    mob_im_pos _ (by simp) (by simp)
  rw [prim_unique (h := fun z => cuspH (LamGL gammaTwoPrime) n f z * z ^ j)
    (fun z hz => momentPrim_hasDerivAt (LamGL (Gamma 2)) n (liftCusp (even_weight hn) f) j z hz)
    (fun z hz => momentPrim_hasDerivAt (LamGL gammaTwoPrime) n f j z hz)
    (momentPrim_zero _ n _ j) (momentPrim_zero _ n _ j) hw]


/-- Restriction of cocycles from `Γ(2)` to `Γ'(2)`. -/
def resLin : cocycles₁ (binRep (Gamma 2) n) →ₗ[ℂ] cocycles₁ (binRep gammaTwoPrime n) where
  toFun c := ⟨fun m => c ⟨m.1, gammaTwoPrime_le m.2⟩, by
    rw [mem_cocycles₁_iff]
    intro g h
    exact (mem_cocycles₁_iff (A := binRep (Gamma 2) n) c).1 c.2
      ⟨g.1, gammaTwoPrime_le g.2⟩ ⟨h.1, gammaTwoPrime_le h.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem resLin_apply (c : cocycles₁ (binRep (Gamma 2) n)) (m : gammaTwoPrime) :
    (resLin c : gammaTwoPrime → binRep gammaTwoPrime n) m = c ⟨m.1, gammaTwoPrime_le m.2⟩ := rfl

theorem neg_one_mem_Gamma2 : (-1 : SL(2, ℤ)) ∈ Gamma 2 := by
  rw [Gamma_mem]; simp

/-- For odd `n`, a cocycle of `Γ(2)` that is a coboundary on `Γ'(2)` is a coboundary. -/
theorem coboundary_of_res (hn : Odd n) (d : cocycles₁ (binRep (Gamma 2) n)) (u : binRep (Gamma 2) n)
    (hu : ∀ m : gammaTwoPrime, d ⟨m.1, gammaTwoPrime_le m.2⟩ =
      (binRep (Gamma 2) n).ρ ⟨m.1, gammaTwoPrime_le m.2⟩ u - u) :
    ∀ g : Gamma 2, d g = (binRep (Gamma 2) n).ρ g u - u := by
  have hc := (mem_cocycles₁_iff (A := binRep (Gamma 2) n) d).1 d.2
  set z : Gamma 2 := ⟨-1, neg_one_mem_Gamma2⟩
  have hρz : ∀ v, (binRep (Gamma 2) n).ρ z v = v := by
    intro v
    rw [TernaryPeriodPolynomials.Argument.ESFoundations.CentralSign.binRep_neg_one
      neg_one_mem_Gamma2]
    have : (-1 : ℂ) ^ (n + 1) = 1 := by
      obtain ⟨t, rfl⟩ := hn
      rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pow_mul]; norm_num
    rw [this, one_smul]
  have hz1 : d z = 0 := by
    have h := hc z z
    have hzz : z * z = 1 := by ext1; simp [z]
    rw [hzz, hρz] at h
    have h1 : d 1 = 0 := by
      have h11 := hc 1 1
      rw [one_mul, (binRep (Gamma 2) n).ρ.map_one, Module.End.one_apply] at h11
      have : d 1 + d 1 = d 1 + 0 := by rw [add_zero]; exact h11.symm
      exact add_left_cancel this
    rw [h1] at h
    have : (2 : ℂ) • d z = 0 := by rw [two_smul]; exact h.symm
    exact (smul_eq_zero.mp this).resolve_left (by norm_num)
  intro g
  rcases mem_or_neg_mem g.2 with h | h
  · exact hu ⟨g.1, h⟩
  · set g' : Gamma 2 := ⟨-g.1, gammaTwoPrime_le h⟩
    have hg : g = z * g' := by ext1; simp [z, g']
    have h1 := hu ⟨-g.1, h⟩
    change d g' = (binRep (Gamma 2) n).ρ g' u - u at h1
    rw [hg, hc, hρz, hz1, add_zero, h1, map_mul, Module.End.mul_apply, hρz]


theorem resLin_holCocycle (hn : Odd n) (f : CuspForm (LamGL gammaTwoPrime) ((n + 3 : ℕ) : ℤ)) :
    resLin (holCocycle (Λ := Gamma 2) (liftCusp (even_weight hn) f)) = holCocycle f := by
  apply Subtype.ext
  funext m
  exact Subtype.ext (eichlerForm_liftCusp hn f m.1)

theorem resLin_antiholCocycle (hn : Odd n)
    (f : CuspForm (LamGL gammaTwoPrime) ((n + 3 : ℕ) : ℤ)) :
    resLin (antiholCocycle (Λ := Gamma 2) (liftCusp (even_weight hn) f)) = antiholCocycle f := by
  apply Subtype.ext
  funext m
  apply Subtype.ext
  change MvPolynomial.map (starRingEnd ℂ) (eichlerForm (Λ := Gamma 2) _ m.1).1 =
    MvPolynomial.map (starRingEnd ℂ) (eichlerForm (Λ := gammaTwoPrime) f m.1).1
  rw [eichlerForm_liftCusp hn f m.1]

/-- **Eichler–Shimura spanning at level two from `Γ'(2)` (odd `n`).** -/
theorem esSpan_gamma2_of_prime (hn : Odd n) (h : ESSpan gammaTwoPrime n) : ESSpan (Gamma 2) n := by
  rintro _ ⟨c, hc, rfl⟩
  have hc' : resLin c ∈ parabolicCocycles gammaTwoPrime n := fun γ hγ => by
    obtain ⟨u, hu⟩ := hc ⟨γ.1, gammaTwoPrime_le γ.2⟩ hγ
    exact ⟨u, hu⟩
  have hx := h ⟨resLin c, hc', rfl⟩
  rw [Submodule.mem_span_set'] at hx
  obtain ⟨k, a, g, hsum⟩ := hx
  have hlift : ∀ i, ∃ κ : cocycles₁ (binRep (Gamma 2) n),
      H1π (binRep (Gamma 2) n) κ ∈
        (Set.range (fun f : CuspForm (LamGL (Gamma 2)) ((n + 3 : ℕ) : ℤ) =>
          H1π (binRep (Gamma 2) n) (holCocycle f)) ∪
        Set.range (fun f : CuspForm (LamGL (Gamma 2)) ((n + 3 : ℕ) : ℤ) =>
          H1π (binRep (Gamma 2) n) (antiholCocycle f))) ∧
      H1π (binRep gammaTwoPrime n) (resLin κ) = (g i : H1 (binRep gammaTwoPrime n)) := by
    intro i
    rcases (g i).2 with ⟨f, hf⟩ | ⟨f, hf⟩
    · exact ⟨holCocycle (liftCusp (even_weight hn) f), Or.inl ⟨_, rfl⟩,
        by rw [resLin_holCocycle hn f]; exact hf⟩
    · exact ⟨antiholCocycle (liftCusp (even_weight hn) f), Or.inr ⟨_, rfl⟩,
        by rw [resLin_antiholCocycle hn f]; exact hf⟩
  choose κ hκS hκg using hlift
  set d : cocycles₁ (binRep (Gamma 2) n) := c - ∑ i, a i • κ i with hd_def
  have hd : H1π (binRep gammaTwoPrime n) (resLin d) = 0 := by
    have e1 : H1π (binRep gammaTwoPrime n) (resLin d) =
        H1π (binRep gammaTwoPrime n) (resLin c) -
          ∑ i, a i • H1π (binRep gammaTwoPrime n) (resLin (κ i)) := by
      rw [hd_def, map_sub, map_sum, map_sub, map_sum]
      simp only [map_smul]
    rw [e1]
    simp only [hκg]
    rw [hsum, sub_self]
  rw [H1π_eq_zero_iff] at hd
  obtain ⟨u, hu⟩ := hd
  have hcob := coboundary_of_res hn d u (fun m => by
    have := congrFun hu m
    rw [d₀₁_hom_apply] at this
    exact this.symm)
  have hd0 : H1π (binRep (Gamma 2) n) d = 0 := by
    rw [H1π_eq_zero_iff]
    refine ⟨u, ?_⟩
    funext g
    rw [d₀₁_hom_apply, hcob g]
  have hcsum : H1π (binRep (Gamma 2) n) c = ∑ i, a i • H1π (binRep (Gamma 2) n) (κ i) := by
    have : H1π (binRep (Gamma 2) n) d =
        H1π (binRep (Gamma 2) n) c - ∑ i, a i • H1π (binRep (Gamma 2) n) (κ i) := by
      rw [hd_def, map_sub, map_sum]
      simp only [map_smul]
    rw [hd0] at this
    exact (sub_eq_zero.mp this.symm)
  change H1π (binRep (Gamma 2) n) c ∈ _
  rw [hcsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hκS i))

end TernaryPeriodPolynomials.Argument.ESFoundations.LevelTwo
