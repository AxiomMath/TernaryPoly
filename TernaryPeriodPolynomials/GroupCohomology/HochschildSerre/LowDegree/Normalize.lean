module

public import TernaryPeriodPolynomials.GroupCohomology.HochschildSerre.LowDegree.Restriction

@[expose] public section


open CategoryTheory CategoryTheory.Limits groupCohomology
noncomputable section
namespace TernaryPoly.LowDegreeHochschildSerre

variable {N Q : Type} [Group N] [Group Q] (φ : Q →* MulAut N)
variable (A : Rep ℚ (G φ))

/-- Vanishing when the first input is in the radical. -/
abbrev FirstNormalized (c : cocycles₂ A) : Prop := ∀ n g, c (nIn φ n,g) = 0

theorem firstNormalized_one_left {c : cocycles₂ A} (hc : FirstNormalized φ A c)
    (g : G φ) : c (1,g) = 0 := by simpa using hc 1 g

theorem firstNormalized_one_right {c : cocycles₂ A} (hc : FirstNormalized φ A c)
    (g : G φ) : c (g,1) = 0 := by
  rw [cocycles₂_map_one_snd, firstNormalized_one_left φ A hc, map_zero]

theorem firstNormalized_equivariance {c : cocycles₂ A} (hc : FirstNormalized φ A c)
    (n : N) (g h : G φ) : c (nIn φ n * g,h) = A.ρ (nIn φ n) (c (g,h)) := by
  have he := (mem_cocycles₂_iff c).mp c.property (nIn φ n) g h
  simpa only [hc, add_zero] using he

/-- Correcting a radical-trivial cocycle makes its first radical input vanish globally. -/
theorem normalize_first_of_restriction_zero (c : cocycles₂ A)
    (hc : ∀ n m, c (nIn φ n,nIn φ m) = 0) :
    ∃ c₁ : cocycles₂ A, H2π A c₁ = H2π A c ∧ FirstNormalized φ A c₁ := by
  let p : G φ → A := fun g => c (nIn φ g.left, qIn φ g.right)
  refine ⟨c + cob₂ φ A p, ?_, ?_⟩
  · rw [map_add]
    exact (congrArg (fun x => H2π A c + x) (H2π_cob₂ φ A p)).trans (add_zero _)
  intro n g
  have h11 : c (1,1) = 0 := by simpa using hc 1 1
  have hn1 : c (nIn φ n,1) = 0 := by rw [cocycles₂_map_one_snd, h11, map_zero]
  have he := (mem_cocycles₂_iff c).mp c.property
    (nIn φ n) (nIn φ g.left) (qIn φ g.right)
  rw [hc, add_zero, SemidirectProduct.inl_left_mul_inr_right] at he
  change c (nIn φ n,g) +
    (A.ρ (nIn φ n) (p g) - p (nIn φ n*g) + p (nIn φ n)) = 0
  change c (nIn φ n,g) +
    (A.ρ (nIn φ n) (c (nIn φ g.left,qIn φ g.right)) -
      c (nIn φ (n * φ 1 g.left),qIn φ (1*g.right)) + c (nIn φ n,qIn φ 1)) = 0
  simp only [map_one, MulAut.one_apply, one_mul, hn1]
  rw [← map_mul] at he
  linear_combination (norm := module) -he

/-- A zero restricted cohomology class permits normalization by actual coboundaries. -/
theorem normalize_first (c : cocycles₂ A)
    (hu : ∃ u : N → A, ∀ n m,
      A.ρ (nIn φ n) (u m) - u (n*m) + u n = c (nIn φ n,nIn φ m)) :
    ∃ c₁ : cocycles₂ A, H2π A c₁ = H2π A c ∧ FirstNormalized φ A c₁ := by
  obtain ⟨u, hu⟩ := hu
  let U : G φ → A := fun g => u g.left
  let c' := c - cob₂ φ A U
  have hc' : ∀ n m, c' (nIn φ n,nIn φ m) = 0 := by
    intro n m
    change c (nIn φ n,nIn φ m) -
      (A.ρ (nIn φ n) (u m) - u (n * φ 1 m) + u n) = 0
    simp only [map_one, MulAut.one_apply, hu, sub_self]
  obtain ⟨c₁, he, hc₁⟩ := normalize_first_of_restriction_zero φ A c' hc'
  refine ⟨c₁, he.trans ?_, hc₁⟩
  change H2π A (c - cob₂ φ A U) = H2π A c
  rw [map_sub]
  exact (congrArg (fun x => H2π A c - x) (H2π_cob₂ φ A U)).trans (sub_zero _)

end TernaryPoly.LowDegreeHochschildSerre
