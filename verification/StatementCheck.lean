import Erdos302

/-! Independent restatements of the original extremal problem, the primitive
relaxation, the full density limit, and the explicit removal and rate bounds. -/

namespace OriginalStatementCheck

def NoTriple (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b → a ≠ c → b ≠ c →
    (1 : ℚ) / a ≠ (1 : ℚ) / b + (1 : ℚ) / c

def MaxCard (N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, NoTriple A ∧ A.card = k} m

theorem predicate_matches (A : Finset ℕ) : NoTriple A ↔ Erdos302.NoUnitFractionTriple A :=
  Iff.rfl

theorem maximum_matches (N m : ℕ) : MaxCard N m ↔ Erdos302.IsMaxNoTripleCard N m :=
  Iff.rfl

theorem ordered_positive_classification (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hbc : b < c) :
    ((1 : ℚ) / a = (1 : ℚ) / b + (1 : ℚ) / c) ↔
    ∃ g u v : ℕ, 0 < g ∧ 0 < u ∧ u < v ∧ Nat.Coprime u v ∧
      a = g * u * v ∧ b = g * u * (u + v) ∧ c = g * v * (u + v) := by
  constructor
  · exact Erdos302.exists_parametrization ha hb hbc
  · rintro ⟨g, u, v, hg, hu, huv, _, rfl, rfl, rfl⟩
    exact (Erdos302.parametric_triple hg hu huv).1

theorem actual_finite_deletion (A : Finset ℕ) :
    ∃ B ⊆ A, NoTriple B ∧ A.card ≤ B.card + (Erdos302.orderedTriples A).card := by
  exact ⟨Erdos302.deleteTriples A, Erdos302.deleteTriples_subset A,
    (predicate_matches _).mpr (Erdos302.deleteTriples_free A), Erdos302.deletion_card_bound A⟩

def RelaxedNoTriple (V : ℕ) (A : Finset ℕ) : Prop :=
  ∀ g u v : ℕ, 0 < g → 0 < u → u < v → Nat.Coprime u v →
    u ∈ Nat.factoredNumbers (Erdos302.primeSet V) →
    v ∈ Nat.factoredNumbers (Erdos302.primeSet V) →
    u + v ∈ Nat.factoredNumbers (Erdos302.primeSet V) →
    g * u * v ∈ A → g * u * (u + v) ∈ A → g * v * (u + v) ∉ A

def RelaxedMaxCard (V N m : ℕ) : Prop :=
  IsGreatest {k | ∃ A ⊆ Finset.Icc 1 N, RelaxedNoTriple V A ∧ A.card = k} m

theorem relaxed_predicate_matches (V : ℕ) (A : Finset ℕ) :
    RelaxedNoTriple V A ↔ Erdos302.RelaxedFree V A := by
  constructor
  · intro h a ha b hb c hc ht
    obtain ⟨g, u, v, hg, hu, huv, hcop, hsU, hsV, hsW, rfl, rfl, rfl⟩ := ht
    exact h g u v hg hu huv hcop hsU hsV hsW ha hb hc
  · intro h g u v hg hu huv hcop hsU hsV hsW ha hb hc
    exact h _ ha _ hb _ hc ⟨g, u, v, hg, hu, huv, hcop, hsU, hsV, hsW, rfl, rfl, rfl⟩

theorem relaxed_maximum_as_stated (V N : ℕ) :
    RelaxedMaxCard V N (Erdos302.relaxedExtremal V N) := by
  obtain ⟨A, hA, hfree, hcard⟩ := Erdos302.exists_maximumCard (Erdos302.relaxedFree_empty V)
    (Finset.Icc 1 N)
  refine ⟨⟨A, hA, (relaxed_predicate_matches V A).mpr hfree, hcard⟩, ?_⟩
  rintro k ⟨B, hB, hgood, hsize⟩
  rw [← hsize]
  exact Erdos302.card_le_maximumCard hB ((relaxed_predicate_matches V B).mp hgood)

theorem full_density_as_stated (f : ℕ → ℕ) (hf : ∀ N, MaxCard N (f N)) :
    Filter.Tendsto (fun N : ℕ => (f N : ℝ) / N) Filter.atTop
      (nhds Erdos302.claimedConstant) := by
  exact Erdos302.densityLimit f (fun N => (maximum_matches N (f N)).mp (hf N))

theorem full_removal_as_stated (N V K f g : ℕ) (hN : 4 ≤ N) (hV : 4 ≤ V)
    (hf : MaxCard N f) (hg : RelaxedMaxCard V N g) :
    0 ≤ (g : ℝ) - f ∧
    (g : ℝ) - f ≤ N * (500000 * (561 / 500 : ℝ) ^ (-(K : ℤ)) +
      10 ^ 23 * (20 / 13 : ℝ) ^ (3 * K) *
        (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ)))) := by
  have hfeq : f = Erdos302.extremal N := Erdos302.isMax_iff_eq_extremal.mp hf
  have hactual := relaxed_maximum_as_stated V N
  have hgeq : g = Erdos302.relaxedExtremal V N := le_antisymm (hactual.2 hg.1) (hg.2 hactual.1)
  subst f
  subst g
  simpa only [Erdos302.Parameters.z, Erdos302.Parameters.q] using
    Erdos302.removalEstimate N V K hN hV

theorem full_effective_rate_as_stated (V : ℕ) (hV : 4 ≤ V) :
    0 ≤ Erdos302.U V - Erdos302.claimedConstant ∧
    Erdos302.U V - Erdos302.claimedConstant ≤ ((10 : ℝ) ^ 23 + 561000) *
      Real.rpow (Real.log V) (-(1 / 140 : ℝ)) :=
  Erdos302.effectiveApproximation V hV

theorem full_rational_enclosures_as_stated (ε : ℚ) (hε : 0 < ε) :
    ∃ a b : ℚ, (a : ℝ) ≤ Erdos302.claimedConstant ∧
      Erdos302.claimedConstant ≤ b ∧ b - a < ε := by
  obtain ⟨V, S, hV, hlow, hupp, hwidth⟩ := Erdos302.rational_enclosures ε hε
  exact ⟨_, _, hlow, hupp, hwidth⟩

theorem original_half_question_as_stated (f : ℕ → ℕ) (hf : ∀ N, MaxCard N (f N)) :
    ¬ Filter.Tendsto (fun N : ℕ => (f N : ℝ) / N) Filter.atTop (nhds (1 / 2 : ℝ)) :=
  Erdos302.density_not_one_half f (fun N => (maximum_matches N (f N)).mp (hf N))

end OriginalStatementCheck
