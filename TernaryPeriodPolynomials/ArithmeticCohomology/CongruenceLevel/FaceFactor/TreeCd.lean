module

public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.TreeRetract
public import TernaryPeriodPolynomials.ArithmeticCohomology.CongruenceLevel.FaceFactor.FreeDecomp

@[expose] public section


/-!
# Bass-Serre dimension shifting

Formalized by Claude Sonnet 5.5.

`cdLe_succ`: if `G` acts on a tree through a surjection `π : G →* Q` (free on vertices and oriented edges) and `ker π` has cohomological dimension `≤ d`, then `G` has cohomological dimension `≤ d + 1` (trivial coefficients).  Proof: the exact sequence `0 → A → Fun(V, A) → Anti(E, A) → 0`, Shapiro's lemma for the permutation modules and the long exact sequence.
-/

noncomputable section

namespace TernaryPeriodPolynomials.Argument.GammaNFaceFactor

open CategoryTheory CategoryTheory.Limits
variable {k : Type} [CommRing k] [Algebra ℚ k] [Invertible (2 : k)] {G Q : Type} [Group G] [Group Q]

/-- **Bass-Serre dimension shifting.**  If `G` acts on a tree through a surjection `π : G →* Q` with free `Q`-action on vertices and oriented edges,
and the kernel of `π` has cohomological dimension `≤ d` (trivial coefficients), then `G` has cohomological dimension `≤ d + 1`. -/
theorem cdLe_succ (π : G →* Q) (hπ : Function.Surjective π) (T : TreeData Q) {d : ℕ} (hS : CdLe k π.ker d) :
    CdLe k G (d + 1) := by
  intro A _ _ n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  let _ : Module ℚ A := Module.compHom A (algebraMap ℚ k)
  have hSES := treeSES_shortExact (k := k) π T A
  -- vertices
  obtain ⟨Iv, ev, hev⟩ := exists_free_decomp Q T.Vt T.free_v
  have hV : IsZero (groupCohomology (treeSES (k := k) π T A).X₂ (n' + 1)) :=
    isZero_perm π T.Vt A ev hev hπ hS (n' + 1) (by omega)
  -- edges
  obtain ⟨Ie, ee, hee⟩ := exists_free_decomp Q T.Et T.free_e
  have hE : IsZero (groupCohomology (Rep.of (permRep (k := k) π T.Et A)) n') :=
    isZero_perm π T.Et A ee hee hπ hS n' (by omega)
  have hAnti : IsZero (groupCohomology (treeSES (k := k) π T A).X₃ n') := isZero_anti π T A hE
  have hepi : Epi (groupCohomology.δ hSES n' (n' + 1) rfl) := groupCohomology.epi_δ_of_isZero hSES n' hV
  exact @IsZero.of_epi _ _ _ _ _ (groupCohomology.δ hSES n' (n' + 1) rfl) hepi hAnti

omit [Algebra ℚ k] [Invertible (2 : k)] in
/-- Cohomological dimension `0`: a subsingleton group. -/
theorem cdLe_zero_of_subsingleton (G : Type) [Group G] [Subsingleton G] : CdLe k G 0 := by
  intro A _ _ n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact isZero_groupCohomology_succ_of_subsingleton (Rep.trivial k G A) m

omit [Algebra ℚ k] [Invertible (2 : k)] in
/-- Cohomological dimension is invariant under isomorphism of groups. -/
theorem CdLe.of_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') {d : ℕ} (h : CdLe k G d) : CdLe k G' d := by
  intro A _ _ n hn
  exact (h A n hn).of_iso
    (groupCohomology.mapIso e (LinearEquiv.refl k A) (fun g => by ext v; simp) n).symm






end TernaryPeriodPolynomials.Argument.GammaNFaceFactor
