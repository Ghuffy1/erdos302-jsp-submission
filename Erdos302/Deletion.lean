import Erdos302.Core

/-! The finite deletion step for the actual reciprocal equation. The cost is
the number of ordered residual triples, with no hidden asymptotic assumption. -/

namespace Erdos302

open Finset

noncomputable def orderedTriples (A : Finset ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (A ×ˢ (A ×ˢ A)).filter (fun t => t.2.1 < t.2.2 ∧
    ReciprocalEquation t.1 t.2.1 t.2.2)

noncomputable def firstVertices (A : Finset ℕ) : Finset ℕ :=
  (orderedTriples A).image Prod.fst

noncomputable def deleteTriples (A : Finset ℕ) : Finset ℕ :=
  A \ firstVertices A

theorem mem_orderedTriples {A : Finset ℕ} {a b c : ℕ} :
    (a, b, c) ∈ orderedTriples A ↔
      a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ b < c ∧ ReciprocalEquation a b c := by
  classical
  simp only [orderedTriples, mem_filter, mem_product]
  tauto

theorem deleteTriples_subset (A : Finset ℕ) : deleteTriples A ⊆ A :=
  Finset.sdiff_subset

theorem deleteTriples_free (A : Finset ℕ) :
    NoUnitFractionTriple (deleteTriples A) := by
  classical
  intro a ha b hb c hc _ _ hbc heq
  obtain ⟨haA, haNot⟩ := Finset.mem_sdiff.mp ha
  have hbA := deleteTriples_subset A hb
  have hcA := deleteTriples_subset A hc
  apply haNot
  rcases lt_or_gt_of_ne hbc with hlt | hgt
  · exact Finset.mem_image.mpr ⟨(a, b, c),
      mem_orderedTriples.mpr ⟨haA, hbA, hcA, hlt, heq⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨(a, c, b),
      mem_orderedTriples.mpr ⟨haA, hcA, hbA, hgt, reciprocalEquation_symm.mp heq⟩,
      rfl⟩

theorem deletion_card_bound (A : Finset ℕ) :
    A.card ≤ (deleteTriples A).card + (orderedTriples A).card := by
  have h := Finset.card_le_card_sdiff_add_card (s := A) (t := firstVertices A)
  have hi : (firstVertices A).card ≤ (orderedTriples A).card := Finset.card_image_le
  exact h.trans (Nat.add_le_add_left hi _)

/-- The deletion argument includes an arbitrary exceptional set, so that its
use with the regularity condition cannot silently omit exceptional vertices. -/
theorem finite_removal_bound {N : ℕ} (A E : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) :
    A.card ≤ extremal N + E.card + (orderedTriples (A \ E)).card := by
  have hsub : deleteTriples (A \ E) ⊆ Finset.Icc 1 N :=
    (deleteTriples_subset _).trans (Finset.sdiff_subset.trans hA)
  have hext := card_le_extremal hsub (deleteTriples_free (A \ E))
  have hdel := deletion_card_bound (A \ E)
  have hcost := Finset.card_le_card_sdiff_add_card (s := A) (t := E)
  omega

end Erdos302
