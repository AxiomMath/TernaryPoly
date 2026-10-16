module

public import TernaryPeriodPolynomials.SymmetricSolution.BoundaryObstruction.Lemma41iiiMixedComponent
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Abel

@[expose] public section


/-!
# Lemma 4.1 (iii): edge injectivity on pure-mixed classes for the bad-line stabilizer

Formalized by Claude Sonnet 5.5.

For the bad-line stabilizer `H = U ⋊ L` (`H = badLineSubgroup`, `U = radicalQ`, `L = leviQ`, in `K†`) and a bar cocycle `c` of `K†` with `PureMixedBadLine c` (only the mixed Hochschild-Serre
term), the vanishing of the mixed component (`MixedComponentZero c`, the class of the crossed cocycle in `H¹(L, H¹(U, E_n))`) is equivalent to the vanishing of the restriction of `[c]` to `H²(H, E_n)`:

* `mixedComponentZero_iff_resH2`: for `PureMixedBadLine c`, `MixedComponentZero c ↔ resH2 … [c] = 0`.  The forward direction is the injectivity of the Hochschild-Serre edge map on pure-mixed classes
  (the filtration steps `E_∞^{2,0}` and `E_∞^{0,2}` are `0`: the pure Levi part vanishes by hypothesis and `H²(L, E^U) = 0` by `leviQ_H2_zero`).  It is proved by hand in bar coordinates
  (`SplitExtension.edge_injective`, an abstract theorem for `H = U ⋊ L`).
* `lemma41_iii_class`: for the class `a_F` of a polynomial functional, vanishing of the mixed component of any pure-mixed representative of `a_F` forces `J_f = 0`; in particular
  the mixed component of `a_F` is zero iff its restriction to the bad-line stabilizer is zero.
-/

open GeneralEisenstein GeneralEisenstein.Homogeneous MvPolynomial
open TernaryPeriodPolynomials.Argument.LevelTransfer
open TernaryPeriodPolynomials.PolynomialBoundaryBridge.Helpers
open TernaryPeriodPolynomials.PolynomialBadLineNormalization
open CategoryTheory Limits

noncomputable section

namespace TernaryPeriodPolynomials.Argument.Identities

namespace SplitExtension

variable {G E : Type} [Group G] [AddCommGroup E] [Module ℂ E]

/-- **Edge injectivity for a split extension `H = U ⋊ L` (abstract form).**  A 2-cocycle `z` on `H` with vanishing pure radical and pure Levi parts, whose mixed edge is a coboundary of `(φ, ε)`
(`φ` a 1-cocycle of `U`, `ε` a 1-cocycle of `L`), is a coboundary on `H`. -/
theorem exists_primitive (ρ : Representation ℂ G E) (H U L : Subgroup G) (z : G → G → E)
    (hD : ∀ g ∈ H, ∀ h ∈ H, ∀ j ∈ H, z (g * h) j + z g h = ρ g (z h j) + z g (h * j))
    (hUH : U ≤ H) (hLH : L ≤ H)
    (hnorm : ∀ l ∈ L, ∀ u ∈ U, l⁻¹ * u * l ∈ U)
    (hdec : ∀ h ∈ H, ∃ u ∈ U, ∃ l ∈ L, h = u * l)
    (hinter : ∀ g ∈ U, g ∈ L → g = 1)
    (zU : ∀ u ∈ U, ∀ u' ∈ U, z u u' = 0) (zL : ∀ l ∈ L, ∀ l' ∈ L, z l l' = 0)
    (φ ε : G → E)
    (hφ : ∀ u ∈ U, ∀ u' ∈ U, φ (u * u') = ρ u (φ u') + φ u)
    (hε : ∀ l ∈ L, ∀ l' ∈ L, ε (l * l') = ρ l (ε l') + ε l)
    (hedge : ∀ l ∈ L, ∀ u ∈ U,
      z l (l⁻¹ * u * l) - z u l = ρ l (φ (l⁻¹ * u * l)) - φ u - (ρ u (ε l) - ε l)) :
    ∃ P : G → E, ∀ h ∈ H, ∀ h' ∈ H, z h h' = ρ h (P h') - P (h * h') + P h := by
  classical
  have hρmul : ∀ g h (x : E), ρ (g * h) x = ρ g (ρ h x) := fun g h x => by simp [map_mul]
  have hρone : ∀ x : E, ρ 1 x = x := fun x => by simp
  have uniq : ∀ u1 ∈ U, ∀ l1 ∈ L, ∀ u2 ∈ U, ∀ l2 ∈ L, u1 * l1 = u2 * l2 → u1 = u2 ∧ l1 = l2 := by
    intro u1 hu1 l1 hl1 u2 hu2 l2 hl2 h
    have hg : u2⁻¹ * u1 = l2 * l1⁻¹ := by
      calc u2⁻¹ * u1 = u2⁻¹ * (u1 * l1) * l1⁻¹ := by group
        _ = u2⁻¹ * (u2 * l2) * l1⁻¹ := by rw [h]
        _ = l2 * l1⁻¹ := by group
    have h1 : u2⁻¹ * u1 = 1 :=
      hinter _ (U.mul_mem (U.inv_mem hu2) hu1) (hg ▸ L.mul_mem hl2 (L.inv_mem hl1))
    have hu : u1 = u2 := by
      have := congrArg (fun x => u2 * x) h1
      simpa using this
    refine ⟨hu, ?_⟩
    subst hu
    exact mul_left_cancel h
  have hdec0 := hdec
  choose! u0 hu0 l0 hl0 hh0 using hdec
  obtain ⟨P, hP⟩ : ∃ P : G → E, ∀ h, P h = φ (u0 h) + ρ (u0 h) (ε (l0 h)) - z (u0 h) (l0 h) :=
    ⟨_, fun _ => rfl⟩
  have Pul : ∀ u ∈ U, ∀ l ∈ L, P (u * l) = φ u + ρ u (ε l) - z u l := by
    intro u hu l hl
    have hH : u * l ∈ H := H.mul_mem (hUH hu) (hLH hl)
    have e := uniq _ (hu0 _ hH) _ (hl0 _ hH) u hu l hl (hh0 _ hH).symm
    rw [hP, e.1, e.2]
  have φ1 : φ 1 = 0 := by
    have h := hφ 1 U.one_mem 1 U.one_mem
    rw [one_mul, hρone] at h
    have h' : φ 1 + 0 = φ 1 + φ 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have ε1 : ε 1 = 0 := by
    have h := hε 1 L.one_mem 1 L.one_mem
    rw [one_mul, hρone] at h
    have h' : ε 1 + 0 = ε 1 + ε 1 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have z11 : z 1 1 = 0 := zU 1 U.one_mem 1 U.one_mem
  have z1l : ∀ l ∈ H, z 1 l = 0 := by
    intro l hl
    have h := hD 1 H.one_mem 1 H.one_mem l hl
    simp only [one_mul, z11, hρone] at h
    exact add_left_cancel h.symm
  have zu1 : ∀ u ∈ H, z u 1 = 0 := by
    intro u hu
    have h := hD u hu 1 H.one_mem 1 H.one_mem
    simp only [mul_one, z11, map_zero] at h
    exact add_right_cancel h
  have Pl : ∀ l ∈ L, P l = ε l := by
    intro l hl
    have h := Pul 1 U.one_mem l hl
    rw [one_mul, φ1, hρone, z1l l (hLH hl)] at h
    simpa using h
  have Pu : ∀ u ∈ U, P u = φ u := by
    intro u hu
    have h := Pul u hu 1 L.one_mem
    rw [mul_one, ε1, map_zero, zu1 u (hUH hu)] at h
    simpa using h
  obtain ⟨W, hW⟩ : ∃ W : G → G → E, ∀ h h', W h h' = z h h' - (ρ h (P h') - P (h * h') + P h) :=
    ⟨_, fun _ _ => rfl⟩
  have hDW : ∀ g ∈ H, ∀ h ∈ H, ∀ j ∈ H,
      ρ g (W h j) - W (g * h) j + W g (h * j) - W g h = 0 := by
    intro g hg h hh j hj
    have e := hD g hg h hh j hj
    have : ρ g (W h j) - W (g * h) j + W g (h * j) - W g h =
        (ρ g (z h j) + z g (h * j)) - (z (g * h) j + z g h) := by
      simp only [hW, map_sub, map_add, hρmul, mul_assoc]
      abel
    rw [this, e, sub_self]
  have hWul : ∀ u ∈ U, ∀ l ∈ L, W u l = 0 := by
    intro u hu l hl
    rw [hW, Pl l hl, Pul u hu l hl, Pu u hu]
    abel
  have hWuu : ∀ u ∈ U, ∀ u' ∈ U, W u u' = 0 := by
    intro u hu u' hu'
    rw [hW, zU u hu u' hu', Pu u' hu', Pu (u * u') (U.mul_mem hu hu'), Pu u hu, hφ u hu u' hu']
    abel
  have hWll : ∀ l ∈ L, ∀ l' ∈ L, W l l' = 0 := by
    intro l hl l' hl'
    rw [hW, zL l hl l' hl', Pl l' hl', Pl (l * l') (L.mul_mem hl hl'), Pl l hl, hε l hl l' hl']
    abel
  have hWlu : ∀ l ∈ L, ∀ u'' ∈ U, W l u'' = 0 := by
    intro l hl u'' hu''
    have hu : l * u'' * l⁻¹ ∈ U := by
      have := hnorm l⁻¹ (L.inv_mem hl) u'' hu''
      simpa using this
    have hc : l⁻¹ * (l * u'' * l⁻¹) * l = u'' := by group
    have hlu : l * u'' = (l * u'' * l⁻¹) * l := by group
    have he := hedge l hl _ hu
    rw [hc] at he
    rw [hW, Pu u'' hu'', Pl l hl, hlu, Pul _ hu l hl]
    calc _ = (z l u'' - z (l * u'' * l⁻¹) l) -
          (ρ l (φ u'') - φ (l * u'' * l⁻¹) - (ρ (l * u'' * l⁻¹) (ε l) - ε l)) := by
            abel
      _ = 0 := by rw [he]; exact sub_self _
  have step1 : ∀ u ∈ U, ∀ h ∈ H, W u h = 0 := by
    intro u hu h hh
    obtain ⟨u'', hu'', l'', hl'', rfl⟩ := hdec0 h hh
    have h1 := hDW u (hUH hu) u'' (hUH hu'') l'' (hLH hl'')
    rw [hWul u'' hu'' l'' hl'', hWul (u * u'') (U.mul_mem hu hu'') l'' hl'', hWuu u hu u'' hu'',
      map_zero] at h1
    simpa using h1
  have step2 : ∀ l ∈ L, ∀ h ∈ H, W l h = 0 := by
    intro l hl h hh
    obtain ⟨u', hu', l', hl', rfl⟩ := hdec0 h hh
    have ht : l * u' * l⁻¹ ∈ U := by
      have := hnorm l⁻¹ (L.inv_mem hl) u' hu'
      simpa using this
    have hlu : l * u' = (l * u' * l⁻¹) * l := by group
    have h1 := hDW l (hLH hl) u' (hUH hu') l' (hLH hl')
    have h2 := hDW (l * u' * l⁻¹) (hUH ht) l (hLH hl) l' (hLH hl')
    rw [hWll l hl l' hl', step1 _ ht (l * l') (H.mul_mem (hLH hl) (hLH hl')), hWul _ ht l hl,
      map_zero] at h2
    have h3 : W (l * u' * l⁻¹ * l) l' = 0 := by simpa using h2
    rw [← hlu] at h3
    rw [hWul u' hu' l' hl', hWlu l hl u' hu', h3, map_zero] at h1
    simpa using h1
  have step3 : ∀ h ∈ H, ∀ j ∈ H, W h j = 0 := by
    intro h hh j hj
    obtain ⟨u, hu, l, hl, rfl⟩ := hdec0 h hh
    have h1 := hDW u (hUH hu) l (hLH hl) j hj
    rw [step2 l hl j hj, step1 u hu (l * j) (H.mul_mem (hLH hl) hj), hWul u hu l hl, map_zero] at h1
    simpa using h1
  refine ⟨P, fun h hh h' hh' => ?_⟩
  have := step3 h hh h' hh'
  rw [hW] at this
  exact sub_eq_zero.mp this


/-- **Correcting the Levi cochain by `H²(L, E^U) = 0`.**  If the defect of `ε₀` from being a 1-cocycle of `L` takes values in the `U`-invariants and `H²(L, M) = 0`
for every complex `L`-module `M`, then `ε₀` can be changed by a `U`-invariant-valued cochain to an actual 1-cocycle without changing its `U`-coboundaries. -/
theorem exists_cocycle_correction (ρ : Representation ℂ G E) (U L : Subgroup G)
    (hnorm : ∀ l ∈ L, ∀ u ∈ U, l⁻¹ * u * l ∈ U)
    (hH2 : ∀ M : Rep.{0} ℂ ↥L, IsZero (groupCohomology M 2)) (ε₀ : G → E)
    (hΩ : ∀ l ∈ L, ∀ l' ∈ L, ∀ u ∈ U,
      ρ u (ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) = ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) :
    ∃ ε : G → E, (∀ l ∈ L, ∀ l' ∈ L, ε (l * l') = ρ l (ε l') + ε l) ∧
      (∀ l ∈ L, ∀ u ∈ U, ρ u (ε l) - ε l = ρ u (ε₀ l) - ε₀ l) := by
  classical
  have hρmul : ∀ g h (x : E), ρ (g * h) x = ρ g (ρ h x) := fun g h x => by simp [map_mul]
  let Mmod : Submodule ℂ E :=
    { carrier := {x | ∀ u ∈ U, ρ u x = x}
      add_mem' := fun {a b} ha hb u hu => by rw [map_add, ha u hu, hb u hu]
      zero_mem' := fun u hu => by simp
      smul_mem' := fun c x hx u hu => by rw [map_smul, hx u hu] }
  have hinv : ∀ l ∈ L, ∀ x ∈ Mmod, ρ l x ∈ Mmod := by
    intro l hl x hx u hu
    have h1 : u * l = l * (l⁻¹ * u * l) := by group
    have h2 : ρ u (ρ l x) = ρ l (ρ (l⁻¹ * u * l) x) := by
      rw [← hρmul, ← hρmul, h1]
    rw [h2]
    show ρ l (ρ (l⁻¹ * u * l) x) = ρ l x
    rw [hx _ (hnorm l hl u hu)]
  let ρM : Representation ℂ ↥L ↥Mmod :=
    { toFun := fun l => (ρ l.1).restrict (fun x hx => hinv l.1 l.2 x hx)
      map_one' := by ext x; simp
      map_mul' := fun a b => by ext x; simp [map_mul] }
  let M : Rep.{0} ℂ ↥L := Rep.of ρM
  let Ω : ↥L × ↥L → ↥Mmod := fun p =>
    ⟨ρ p.1 (ε₀ p.2) - ε₀ (p.1 * p.2) + ε₀ p.1, fun u hu => hΩ p.1 p.1.2 p.2 p.2.2 u hu⟩
  have hΩc : (Ω : ↥L × ↥L → M.V) ∈ groupCohomology.cocycles₂ M := by
    rw [groupCohomology.mem_cocycles₂_iff]
    intro g h j
    apply Subtype.ext
    show (ρ ((g * h : ↥L) : G) (ε₀ j) - ε₀ (((g * h : ↥L) : G) * j) + ε₀ ((g * h : ↥L) : G)) +
        (ρ (g : G) (ε₀ h) - ε₀ ((g : G) * h) + ε₀ g) =
      ρ (g : G) (ρ h (ε₀ j) - ε₀ ((h : G) * j) + ε₀ h) +
        (ρ (g : G) (ε₀ ((h : G) * j)) - ε₀ ((g : G) * ((h : G) * j)) + ε₀ g)
    simp only [Subgroup.coe_mul, hρmul, map_add, map_sub, mul_assoc]
    abel
  have hz : groupCohomology.H2π M ⟨Ω, hΩc⟩ = 0 :=
    (ModuleCat.subsingleton_of_isZero (hH2 M)).elim _ _
  rw [groupCohomology.H2π_eq_zero_iff] at hz
  obtain ⟨y, hy⟩ := hz
  have hy' : ∀ a b : ↥L, ρ (a : G) ((y b : ↥Mmod) : E) - ((y (a * b) : ↥Mmod) : E) + ((y a : ↥Mmod) : E) =
      ρ a (ε₀ b) - ε₀ ((a : G) * b) + ε₀ a := by
    intro a b
    have := congrFun hy (a, b)
    simp only [groupCohomology.d₁₂_hom_apply] at this
    exact congrArg Subtype.val this
  refine ⟨fun g => ε₀ g - (if hg : g ∈ L then ((y ⟨g, hg⟩ : ↥Mmod) : E) else 0), ?_, ?_⟩
  · intro l hl l' hl'
    simp only [dite_eq_left hl, dite_eq_left hl', dite_eq_left (L.mul_mem hl hl')]
    have h := hy' ⟨l, hl⟩ ⟨l', hl'⟩
    have e : (⟨l, hl⟩ * ⟨l', hl'⟩ : ↥L) = ⟨l * l', L.mul_mem hl hl'⟩ := rfl
    rw [e] at h
    have key : ε₀ (l * l') - ((y ⟨l * l', L.mul_mem hl hl'⟩ : ↥Mmod) : E) -
        (ρ l (ε₀ l' - ((y ⟨l', hl'⟩ : ↥Mmod) : E)) + (ε₀ l - ((y ⟨l, hl⟩ : ↥Mmod) : E))) =
      (ρ l ((y ⟨l', hl'⟩ : ↥Mmod) : E) - ((y ⟨l * l', L.mul_mem hl hl'⟩ : ↥Mmod) : E) +
        ((y ⟨l, hl⟩ : ↥Mmod) : E)) - (ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) := by
      simp only [map_sub]; abel
    rw [← sub_eq_zero, key]
    exact sub_eq_zero.mpr h
  · intro l hl u hu
    simp only [dite_eq_left hl, map_sub]
    have hyu : ρ u ((y ⟨l, hl⟩ : ↥Mmod) : E) = ((y ⟨l, hl⟩ : ↥Mmod) : E) := (y ⟨l, hl⟩).2 u hu
    rw [hyu]
    abel


/-- **The defect of the Levi choices lies in the `U`-invariants** (the cocycle property of the mixed edge, from the 2-cocycle identity and the vanishing pure Levi part). -/
theorem defect_invariant (ρ : Representation ℂ G E) (H U L : Subgroup G) (z : G → G → E)
    (hD : ∀ g ∈ H, ∀ h ∈ H, ∀ j ∈ H, z (g * h) j + z g h = ρ g (z h j) + z g (h * j))
    (hUH : U ≤ H) (hLH : L ≤ H)
    (hnorm : ∀ l ∈ L, ∀ u ∈ U, l⁻¹ * u * l ∈ U)
    (zL : ∀ l ∈ L, ∀ l' ∈ L, z l l' = 0)
    (φ ε₀ : G → E)
    (hedge₀ : ∀ l ∈ L, ∀ u ∈ U,
      z l (l⁻¹ * u * l) - z u l = ρ l (φ (l⁻¹ * u * l)) - φ u - (ρ u (ε₀ l) - ε₀ l)) :
    ∀ l ∈ L, ∀ l' ∈ L, ∀ u ∈ U,
      ρ u (ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) = ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l := by
  intro l hl l' hl' u hu
  have hρmul : ∀ g h (x : E), ρ (g * h) x = ρ g (ρ h x) := fun g h x => by simp [map_mul]
  have hu' : l⁻¹ * u * l ∈ U := hnorm l hl u hu
  have hu'' : l'⁻¹ * (l⁻¹ * u * l) * l' ∈ U := hnorm l' hl' _ hu'
  have p1 : u * l = l * (l⁻¹ * u * l) := by group
  have p2 : (l⁻¹ * u * l) * l' = l' * (l'⁻¹ * (l⁻¹ * u * l) * l') := by group
  have p3 : (l * l')⁻¹ * u * (l * l') = l'⁻¹ * (l⁻¹ * u * l) * l' := by group
  have E1 := hedge₀ l hl u hu
  have E2 := hedge₀ l' hl' _ hu'
  have E3 := hedge₀ (l * l') (L.mul_mem hl hl') u hu
  rw [p3] at E3
  have D1 := hD l (hLH hl) l' (hLH hl') _ (hUH hu'')
  have D2 := hD u (hUH hu) l (hLH hl) l' (hLH hl')
  have D3 := hD l (hLH hl) _ (hUH hu') l' (hLH hl')
  rw [← p2, zL l hl l' hl'] at D1
  rw [← p1] at D3
  rw [zL l hl l' hl', map_zero] at D2
  have key : ∀ x : E, ρ l (ρ (l⁻¹ * u * l) x) = ρ u (ρ l x) := by
    intro x
    rw [← hρmul, ← hρmul, ← p1]
  have cr : z (l * l') (l'⁻¹ * (l⁻¹ * u * l) * l') - z u (l * l') =
      ρ l (z l' (l'⁻¹ * (l⁻¹ * u * l) * l') - z (l⁻¹ * u * l) l') +
        (z l (l⁻¹ * u * l) - z u l) := by
    have h0 : (z (l * l') (l'⁻¹ * (l⁻¹ * u * l) * l') - z u (l * l')) -
        (ρ l (z l' (l'⁻¹ * (l⁻¹ * u * l) * l') - z (l⁻¹ * u * l) l') +
          (z l (l⁻¹ * u * l) - z u l)) =
        ((z (l * l') (l'⁻¹ * (l⁻¹ * u * l) * l') + 0) -
            (ρ l (z l' (l'⁻¹ * (l⁻¹ * u * l) * l')) + z l ((l⁻¹ * u * l) * l'))) -
          ((z (u * l) l' + z l (l⁻¹ * u * l)) -
            (ρ l (z (l⁻¹ * u * l) l') + z l ((l⁻¹ * u * l) * l'))) +
          ((z (u * l) l' + z u l) - (0 + z u (l * l'))) := by
      simp only [map_sub]; abel
    rw [← sub_eq_zero, h0, D1, D3, D2]
    simp
  have Eq : ρ (l * l') (φ (l'⁻¹ * (l⁻¹ * u * l) * l')) - φ u - (ρ u (ε₀ (l * l')) - ε₀ (l * l')) =
      ρ l (ρ l' (φ (l'⁻¹ * (l⁻¹ * u * l) * l')) - φ (l⁻¹ * u * l) -
          (ρ (l⁻¹ * u * l) (ε₀ l') - ε₀ l')) +
        (ρ l (φ (l⁻¹ * u * l)) - φ u - (ρ u (ε₀ l) - ε₀ l)) := by
    rw [← E3, ← E2, ← E1]
    exact cr
  have h0 := sub_eq_zero.mpr Eq
  have hrel : ρ u (ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) - (ρ l (ε₀ l') - ε₀ (l * l') + ε₀ l) =
      (ρ (l * l') (φ (l'⁻¹ * (l⁻¹ * u * l) * l')) - φ u - (ρ u (ε₀ (l * l')) - ε₀ (l * l'))) -
        (ρ l (ρ l' (φ (l'⁻¹ * (l⁻¹ * u * l) * l')) - φ (l⁻¹ * u * l) -
          (ρ (l⁻¹ * u * l) (ε₀ l') - ε₀ l')) +
        (ρ l (φ (l⁻¹ * u * l)) - φ u - (ρ u (ε₀ l) - ε₀ l))) := by
    simp only [map_sub, map_add]
    rw [key]
    simp only [hρmul]
    abel
  exact sub_eq_zero.mp (hrel.trans h0)

/-- **Edge injectivity for the split extension `H = U ⋊ L` (abstract master theorem).**  Hypotheses: the 2-cocycle identity of `z` on `H`; `H = U L` with `U ∩ L = 1`, `L` normalizing `U`;
vanishing pure radical and pure Levi parts of `z`; a 1-cocycle `φ` of `U` and Levi choices `ε₀` with the mixed edge equal to `L φ - φ - (U ε₀ - ε₀)` (the mixed class is a coboundary);
and `H²(L, M) = 0` for every complex `L`-module `M`.  Then `z` is a coboundary on `H`. -/
theorem edge_injective (ρ : Representation ℂ G E) (H U L : Subgroup G) (z : G → G → E)
    (hD : ∀ g ∈ H, ∀ h ∈ H, ∀ j ∈ H, z (g * h) j + z g h = ρ g (z h j) + z g (h * j))
    (hUH : U ≤ H) (hLH : L ≤ H)
    (hnorm : ∀ l ∈ L, ∀ u ∈ U, l⁻¹ * u * l ∈ U)
    (hdec : ∀ h ∈ H, ∃ u ∈ U, ∃ l ∈ L, h = u * l)
    (hinter : ∀ g ∈ U, g ∈ L → g = 1)
    (zU : ∀ u ∈ U, ∀ u' ∈ U, z u u' = 0) (zL : ∀ l ∈ L, ∀ l' ∈ L, z l l' = 0)
    (hH2 : ∀ M : Rep.{0} ℂ ↥L, IsZero (groupCohomology M 2))
    (φ : G → E)
    (hφ : ∀ u ∈ U, ∀ u' ∈ U, φ (u * u') = ρ u (φ u') + φ u)
    (ε₀ : G → E)
    (hedge₀ : ∀ l ∈ L, ∀ u ∈ U,
      z l (l⁻¹ * u * l) - z u l = ρ l (φ (l⁻¹ * u * l)) - φ u - (ρ u (ε₀ l) - ε₀ l)) :
    ∃ P : G → E, ∀ h ∈ H, ∀ h' ∈ H, z h h' = ρ h (P h') - P (h * h') + P h := by
  obtain ⟨ε, hε, hεu⟩ := exists_cocycle_correction ρ U L hnorm hH2 ε₀
    (defect_invariant ρ H U L z hD hUH hLH hnorm zL φ ε₀ hedge₀)
  exact exists_primitive ρ H U L z hD hUH hLH hnorm hdec hinter zU zL φ ε hφ hε
    (fun l hl u hu => by rw [hedge₀ l hl u hu, hεu l hl u hu])


end SplitExtension

section Concrete

open Matrix

variable {n : ℕ}

local notation "ρ" => rationalCoefficientComponent n trivialCharacter

/-- The inhomogeneous 2-cochain `z(a, b) = c(1, a, ab)` of a bar cocycle. -/
def barZ (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) (a b : RationalGL3) :
    HomogeneousPoly n :=
  c.val.val ![1, a, a * b]

theorem lineUnipotent_mem_lineParabolic (s t : ℚ) :
    (Adelic.lineUnipotent s t) ∈ Adelic.lineParabolic ℚ :=
  ⟨by simp [Adelic.lineUnipotent, Adelic.upperUnipotent], by simp [Adelic.lineUnipotent, Adelic.upperUnipotent]⟩

theorem radicalQ_le_badLine : radicalQ ≤ badLineSubgroup := by
  intro g hg
  obtain ⟨s, t, rfl⟩ := (mem_radicalQ g).mp hg
  exact ⟨radicalQ_le hg, lineUnipotent_mem_lineParabolic _ _⟩

theorem leviQ_le_badLine : leviQ ≤ badLineSubgroup := by
  intro g hg
  refine ⟨leviQ_le hg, ?_⟩
  obtain ⟨l, ⟨_, _, _, h10, h20⟩, rfl⟩ := (mem_leviQ g).mp hg
  exact ⟨by simp [GeneralLinearGroup.map_apply, h10], by simp [GeneralLinearGroup.map_apply, h20]⟩

theorem map_integralLineUnipotent (s t : ℤ) :
    GeneralLinearGroup.map (Int.castRingHom ℚ) (Adelic.lineUnipotent s t) =
      Adelic.lineUnipotent (s : ℚ) (t : ℚ) := by
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Adelic.lineUnipotent, Adelic.upperUnipotent, GeneralLinearGroup.map_apply, Matrix.cons_val_two]

/-- **`H = U ⋊ L`**: every element of the bad-line stabilizer is `u l` with `u` in the integral radical and `l` in the integral Levi. -/
theorem badLine_decomposition {h : RationalGL3} (hh : h ∈ badLineSubgroup) :
    ∃ u ∈ radicalQ, ∃ l ∈ leviQ, h = u * l := by
  obtain ⟨integral, integral_eq⟩ := hh.1
  have heq : GeneralLinearGroup.map (Int.castRingHom ℚ) integral.val = h := integral_eq
  have hline : h ∈ Adelic.lineParabolic ℚ := hh.2
  have integral_line : integral.val ∈ Adelic.lineParabolic ℤ := by
    constructor
    · have coordinate := hline.1
      rw [← heq] at coordinate
      change ((integral.val.val 1 0 : ℤ) : ℚ) = 0 at coordinate
      exact_mod_cast coordinate
    · have coordinate := hline.2
      rw [← heq] at coordinate
      change ((integral.val.val 2 0 : ℤ) : ℚ) = 0 at coordinate
      exact_mod_cast coordinate
  have hlh : BadLineLevi (lineLevi ⟨integral.val, integral_line⟩) :=
    ⟨lineLevi_arithmetic integral.property integral_line, rfl, rfl, rfl, rfl⟩
  have huh := lineRadical_upper (⟨integral.val, integral_line⟩ : Adelic.lineParabolic ℤ)
  have hprod := lineRadical_times_levi (⟨integral.val, integral_line⟩ : Adelic.lineParabolic ℤ)
  refine ⟨GeneralLinearGroup.map (Int.castRingHom ℚ) (lineRadical ⟨integral.val, integral_line⟩), ?_,
    GeneralLinearGroup.map (Int.castRingHom ℚ) (lineLevi ⟨integral.val, integral_line⟩),
    (mem_leviQ _).mpr ⟨_, hlh, rfl⟩, ?_⟩
  · rw [mem_radicalQ]
    refine ⟨(lineRadical ⟨integral.val, integral_line⟩).val 0 1,
      (lineRadical ⟨integral.val, integral_line⟩).val 0 2, ?_⟩
    rw [← map_integralLineUnipotent, ← huh]
  · rw [← heq, ← map_mul, hprod]

theorem radicalQ_inter_leviQ {g : RationalGL3} (hU : g ∈ radicalQ) (hL : g ∈ leviQ) : g = 1 := by
  obtain ⟨s, t, rfl⟩ := (mem_radicalQ g).mp hU
  obtain ⟨l, ⟨_, h01, h02, _, _⟩, hl⟩ := (mem_leviQ _).mp hL
  have h01' : (l : Matrix (Fin 3) (Fin 3) ℤ) 0 1 = 0 := h01
  have h02' : (l : Matrix (Fin 3) (Fin 3) ℤ) 0 2 = 0 := h02
  have e1 := congrArg (fun g : RationalGL3 => g.val 0 1) hl
  have e2 := congrArg (fun g : RationalGL3 => g.val 0 2) hl
  simp only [Adelic.lineUnipotent, Adelic.upperUnipotent, GeneralLinearGroup.map_apply] at e1 e2
  have hs : (s : ℚ) = 0 := by simpa [h01'] using e1
  have ht : (t : ℚ) = 0 := by simpa [h02'] using e2
  rw [hs, ht]
  apply GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [Adelic.lineUnipotent, Adelic.upperUnipotent]

/-- The 2-cocycle identity of `z = barZ c` on the bad-line stabilizer (from the bridge to Mathlib's inhomogeneous cocycles). -/
theorem barZ_cocycle (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)) :
    ∀ g ∈ badLineSubgroup, ∀ h ∈ badLineSubgroup, ∀ j ∈ badLineSubgroup,
      barZ c (g * h) j + barZ c g h = ρ g (barZ c h j) + barZ c g (h * j) := by
  intro g hg h hh j hj
  have hf : (⇑(bridgeCocycle (rationalCoefficientComponent n trivialCharacter) rationalLevel c) :
      ↥rationalLevel × ↥rationalLevel → HomogeneousPoly n) ∈
      groupCohomology.cocycles₂
        (Rep.of ((rationalCoefficientComponent n trivialCharacter).comp rationalLevel.subtype)) :=
    (bridgeCocycle (rationalCoefficientComponent n trivialCharacter) rationalLevel c).2
  rw [groupCohomology.mem_cocycles₂_iff] at hf
  have := hf ⟨g, hg.1⟩ ⟨h, hh.1⟩ ⟨j, hj.1⟩
  simp only [bridgeCocycle_apply] at this
  exact this

theorem barZ_radical {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hpure : PureMixedBadLine c) :
    ∀ u ∈ radicalQ, ∀ u' ∈ radicalQ, barZ c u u' = 0 := by
  intro u hu u' hu'
  obtain ⟨s, t, rfl⟩ := (mem_radicalQ u).mp hu
  obtain ⟨s', t', rfl⟩ := (mem_radicalQ u').mp hu'
  exact hpure.1 s t s' t'

theorem barZ_levi {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hpure : PureMixedBadLine c) :
    ∀ l ∈ leviQ, ∀ l' ∈ leviQ, barZ c l l' = 0 := by
  intro l hl l' hl'
  obtain ⟨a, ha, rfl⟩ := (mem_leviQ l).mp hl
  obtain ⟨b, hb, rfl⟩ := (mem_leviQ l').mp hl'
  have := hpure.2 a b ha hb
  unfold barZ
  rw [← map_mul]
  exact this

theorem barZ_edge (c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter))
    (l u : RationalGL3) :
    (barZ c l (l⁻¹ * u * l) - barZ c u l).val = mixedBarEdge c l u := by
  unfold barZ mixedBarEdge
  have e : l * (l⁻¹ * u * l) = u * l := by group
  rw [e]
  rfl

theorem leviQ_normalizes {l u : RationalGL3} (hl : l ∈ leviQ) (hu : u ∈ radicalQ) :
    l⁻¹ * u * l ∈ radicalQ := by
  have := leviQ_normalizes_radicalQ (leviQ.inv_mem hl) hu
  simpa using this

end Concrete


section Main

variable {n : ℕ}

local notation "ρ" => rationalCoefficientComponent n trivialCharacter

theorem badLine_le_level : badLineSubgroup ≤ rationalLevel := inf_le_left

/-- **Edge injectivity, first half**: a pure-mixed cocycle with vanishing mixed component is a coboundary on the bad-line stabilizer. -/
theorem primitive_of_mixedComponentZero
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hpure : PureMixedBadLine c) (hmix : MixedComponentZero c) :
    ∃ P : RationalGL3 → HomogeneousPoly n, ∀ h ∈ badLineSubgroup, ∀ h' ∈ badLineSubgroup,
      barZ c h h' = ρ h (P h') - P (h * h') + P h := by
  obtain ⟨φ, hφ, hl⟩ := hmix
  choose! ε₀ hε₀ using hl
  refine SplitExtension.edge_injective (rationalCoefficientComponent n trivialCharacter) badLineSubgroup
    radicalQ leviQ (barZ c) (barZ_cocycle c) radicalQ_le_badLine leviQ_le_badLine
    (fun l hl u hu => leviQ_normalizes hl hu) (fun h hh => badLine_decomposition hh)
    (fun g hU hL => radicalQ_inter_leviQ hU hL) (barZ_radical hpure) (barZ_levi hpure)
    (fun M => leviQ_H2_zero M) φ hφ ε₀ ?_
  intro l hl u hu
  apply Subtype.ext
  have h1 := barZ_edge c l u
  rw [hε₀ l hl u hu] at h1
  simpa only [Submodule.coe_sub] using h1

theorem resH2_badLine_zero_of_primitive
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (P : badLineSubgroup → HomogeneousPoly n)
    (hP : ∀ a b : badLineSubgroup,
      c.val.val ![1, (a : RationalGL3), ((a * b : badLineSubgroup) : RationalGL3)] =
        ρ a (P b) - P (a * b) + P a) :
    resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
  apply (bridge (rationalCoefficientComponent n trivialCharacter) badLineSubgroup).injective
  have h1 : resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) =
      Submodule.Quotient.mk (cocyclesRes (rationalCoefficientComponent n trivialCharacter) badLine_le_level c) := rfl
  rw [h1, bridge_mk, LinearEquiv.map_zero, groupCohomology.H2π_eq_zero_iff]
  refine ⟨P, ?_⟩
  funext p
  rw [groupCohomology.d₁₂_hom_apply, bridgeCocycle_apply]
  exact (hP p.1 p.2).symm

theorem primitive_of_resH2_zero
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (h : resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0) :
    ∃ P : badLineSubgroup → HomogeneousPoly n, ∀ a b : badLineSubgroup,
      c.val.val ![1, (a : RationalGL3), ((a * b : badLineSubgroup) : RationalGL3)] =
        ρ a (P b) - P (a * b) + P a := by
  have h1 : bridge (rationalCoefficientComponent n trivialCharacter) badLineSubgroup
      (resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) = 0 := by
    rw [h, LinearEquiv.map_zero]
  have h2 : resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) =
      Submodule.Quotient.mk (cocyclesRes (rationalCoefficientComponent n trivialCharacter) badLine_le_level c) := rfl
  rw [h2, bridge_mk, groupCohomology.H2π_eq_zero_iff] at h1
  obtain ⟨P, hP⟩ := h1
  refine ⟨P, fun a b => ?_⟩
  have := congrFun hP (a, b)
  rw [groupCohomology.d₁₂_hom_apply, bridgeCocycle_apply] at this
  exact this.symm

/-- A primitive on the bad-line stabilizer gives the vanishing of the mixed component (for a cocycle with vanishing pure radical part). -/
theorem mixedComponentZero_of_primitive
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hrad : ∀ u ∈ radicalQ, ∀ u' ∈ radicalQ, barZ c u u' = 0)
    (P : badLineSubgroup → HomogeneousPoly n)
    (hP : ∀ a b : badLineSubgroup,
      c.val.val ![1, (a : RationalGL3), ((a * b : badLineSubgroup) : RationalGL3)] =
        ρ a (P b) - P (a * b) + P a) :
    MixedComponentZero c := by
  classical
  refine ⟨fun g => if hg : g ∈ badLineSubgroup then P ⟨g, hg⟩ else 0, ?_, ?_⟩
  · intro u hu u' hu'
    have hu1 := radicalQ_le_badLine hu
    have hu2 := radicalQ_le_badLine hu'
    have hu3 := radicalQ_le_badLine (radicalQ.mul_mem hu hu')
    simp only [dite_eq_left hu1, dite_eq_left hu2, dite_eq_left hu3]
    have h0 : ρ u (P ⟨u', hu2⟩) - P ⟨u * u', hu3⟩ + P ⟨u, hu1⟩ = 0 := by
      have e : c.val.val ![1, u, u * u'] = ρ u (P ⟨u', hu2⟩) - P ⟨u * u', hu3⟩ + P ⟨u, hu1⟩ :=
        hP ⟨u, hu1⟩ ⟨u', hu2⟩
      rw [← e]
      exact hrad u hu u' hu'
    rw [sub_add_eq_add_sub, sub_eq_zero] at h0
    exact h0.symm
  · intro l hl
    have hl1 := leviQ_le_badLine hl
    refine ⟨P ⟨l, hl1⟩, fun u hu => ?_⟩
    have hu1 := radicalQ_le_badLine hu
    have hcon : l⁻¹ * u * l ∈ badLineSubgroup :=
      badLineSubgroup.mul_mem (badLineSubgroup.mul_mem (badLineSubgroup.inv_mem hl1) hu1) hl1
    have key := mixedBarEdge_of_linePrimitive c P hP ⟨l, hl1⟩ ⟨u, hu1⟩
    simp only [dite_eq_left hcon, dite_eq_left hu1]
    exact key

/-- **Lemma 4.1 (iii), edge injectivity**: for a pure-mixed cocycle, the mixed Hochschild-Serre component vanishes iff the restriction of its class to the bad-line stabilizer vanishes. -/
theorem mixedComponentZero_iff_resH2
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hpure : PureMixedBadLine c) :
    MixedComponentZero c ↔
      resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level
        (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c) = 0 := by
  constructor
  · intro hmix
    obtain ⟨P, hP⟩ := primitive_of_mixedComponentZero hpure hmix
    exact resH2_badLine_zero_of_primitive (fun h => P h.val) (fun a b => hP a a.2 b b.2)
  · intro h
    obtain ⟨P, hP⟩ := primitive_of_resH2_zero h
    exact mixedComponentZero_of_primitive (barZ_radical hpure) P hP

/-- The mixed component of a class that has a pure-mixed representative: it vanishes for some (equivalently every) pure-mixed representative. -/
def MixedComponentZeroClass (a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)) : Prop :=
  ∃ c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter),
    classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c = a ∧
      PureMixedBadLine c ∧ MixedComponentZero c

theorem mixedComponentZeroClass_iff
    {a : H2 rationalLevel (rationalCoefficientComponent n trivialCharacter)} (ha : PureMixedClass a) :
    MixedComponentZeroClass a ↔
      resH2 (rationalCoefficientComponent n trivialCharacter) badLine_le_level a = 0 := by
  constructor
  · rintro ⟨c, rfl, hp, hm⟩
    exact (mixedComponentZero_iff_resH2 hp).mp hm
  · intro h
    obtain ⟨c, rfl, hp⟩ := ha
    exact ⟨c, rfl, hp, (mixedComponentZero_iff_resH2 hp).mpr h⟩

/-- **Lemma 4.1 (iii), class form**.  For the class `a_F` of any cocycle realizing any path family of a polynomial functional `F` of a symmetric solution `f`: if the mixed
Hochschild-Serre component of `a_F` is zero (for a pure-mixed representative; `a_F` has one by `lemma41_i_class`), then `J_f = 0` as a polynomial.  By `mixedComponentZeroClass_iff` the hypothesis is equivalent
to `res_{H} a_F = 0` in `H²(H, E_n)`, `H` the bad-line stabilizer. -/
theorem lemma41_iii_class {f : HomogeneousPoly n} (hn : 0 < n) (solution : SymmetricSolution f)
    {F : EdgeChains →ₗ[ℂ] HomogeneousPoly n} (hF : IsPolynomialFunctional f F)
    {τ : rationalLevel → EdgeChains} (hτ : IsPathFamily τ)
    {c : cocycles rationalLevel (rationalCoefficientComponent n trivialCharacter)}
    (hc : RealizesPathClass F τ c)
    (hmix : MixedComponentZeroClass
      (classOf rationalLevel (rationalCoefficientComponent n trivialCharacter) c)) :
    bernoulliObstruction f = 0 := by
  have hres := (mixedComponentZeroClass_iff (lemma41_i_class hF hτ hc)).mp hmix
  have hcs := pathCocycle_realizes hF specialPaths_isPathFamily
  have hclass := realizesPathClass_class_independent hF specialPaths_isPathFamily hτ hcs hc
  have hmixs : MixedComponentZero (pathCocycle hF specialPaths_isPathFamily) :=
    (mixedComponentZero_iff_resH2 (specialPathCocycle_pureMixed hF)).mpr (by rw [hclass]; exact hres)
  exact lemma41_iii hn solution hF hmixs

end Main

end TernaryPeriodPolynomials.Argument.Identities
