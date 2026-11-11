import Erdos302.ExceptionalSet
import Erdos302.Deletion
import Erdos302.Specification

namespace Erdos302

theorem smooth_of_le_two_mul {n V : ℕ} (hn : 0 < n) (hnV : n ≤ 2 * V) :
    n ∈ Nat.factoredNumbers (primeSet V) := by
  apply Nat.mem_factoredNumbers_iff_forall_le.mpr
  refine ⟨hn.ne', ?_⟩
  intro p hpn hp hpdvd
  simp only [primeSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hp⟩

theorem retained_of_parameter_le {g u v V : ℕ}
    (hg : 0 < g) (hu : 0 < u) (huv : u < v) (hcop : Nat.Coprime u v) (hvV : v ≤ V) :
    RetainedTriple V (g * u * v) (g * u * (u + v)) (g * v * (u + v)) := by
  refine ⟨g, u, v, hg, hu, huv, hcop, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · exact smooth_of_le_two_mul hu (by omega)
  · exact smooth_of_le_two_mul (by omega) (by omega)
  · exact smooth_of_le_two_mul (by omega) (by omega)

def tripleOfParameters (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (t.1 * t.2.1 * t.2.2,
    t.1 * t.2.1 * (t.2.1 + t.2.2), t.1 * t.2.2 * (t.2.1 + t.2.2))

noncomputable def largeRegularParameters (N V K : ℕ) : Finset (ℕ × ℕ × ℕ) := by
  classical
  let I := Finset.Icc 1 N
  exact (I ×ˢ (I ×ˢ I)).filter (fun t =>
    t.2.1 < t.2.2 ∧ V < t.2.2 ∧ Nat.Coprime t.2.1 t.2.2 ∧
    t.1 * t.2.2 * (t.2.1 + t.2.2) ≤ N ∧
    KRegular K (t.1 * t.2.1 * t.2.2) ∧
    KRegular K (t.1 * t.2.1 * (t.2.1 + t.2.2)) ∧
    KRegular K (t.1 * t.2.2 * (t.2.1 + t.2.2)))

theorem mem_largeRegularParameters {N V K g u v : ℕ} :
    (g, u, v) ∈ largeRegularParameters N V K ↔
      (1 ≤ g ∧ g ≤ N) ∧ (1 ≤ u ∧ u ≤ N) ∧ (1 ≤ v ∧ v ≤ N) ∧
      u < v ∧ V < v ∧ Nat.Coprime u v ∧ g * v * (u + v) ≤ N ∧
      KRegular K (g * u * v) ∧ KRegular K (g * u * (u + v)) ∧
      KRegular K (g * v * (u + v)) := by
  classical
  simp only [largeRegularParameters, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  tauto

theorem residual_triples_le_parameters {N V K : ℕ} (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (hfree : RelaxedFree V A) :
    (orderedTriples (A \ irregularVertices N K)).card ≤
      (largeRegularParameters N V K).card := by
  classical
  have hreg (n : ℕ) (hn : n ∈ A \ irregularVertices N K) : KRegular K n := by
    obtain ⟨hnA, hnE⟩ := Finset.mem_sdiff.mp hn
    by_contra hnot
    exact hnE (Finset.mem_filter.mpr ⟨hA hnA, hnot⟩)
  have hsub : orderedTriples (A \ irregularVertices N K) ⊆
      (largeRegularParameters N V K).image tripleOfParameters := by
    rintro ⟨a, b, c⟩ ht
    obtain ⟨ha, hb, hc, hbc, heq⟩ := mem_orderedTriples.mp ht
    have haA := (Finset.mem_sdiff.mp ha).1
    have hbA := (Finset.mem_sdiff.mp hb).1
    have hcA := (Finset.mem_sdiff.mp hc).1
    obtain ⟨ha1, haN⟩ := Finset.mem_Icc.mp (hA haA)
    obtain ⟨hb1, hbN⟩ := Finset.mem_Icc.mp (hA hbA)
    obtain ⟨hc1, hcN⟩ := Finset.mem_Icc.mp (hA hcA)
    obtain ⟨g, u, v, hg, hu, huv, hcop, hpa, hpb, hpc⟩ :=
      exists_parametrization (by omega) (by omega) hbc heq
    have hv : 0 < v := by omega
    have hw : 0 < u + v := by omega
    have hgv : g * v ≤ c := by rw [hpc]; exact Nat.le_mul_of_pos_right _ hw
    have hgN : g ≤ N := (Nat.le_mul_of_pos_right g hv).trans (hgv.trans hcN)
    have hvN : v ≤ N := (Nat.le_mul_of_pos_left v hg).trans (hgv.trans hcN)
    have huN : u ≤ N := huv.le.trans hvN
    have hVv : V < v := by
      by_contra hnot
      have hvV : v ≤ V := by omega
      have hret := retained_of_parameter_le hg hu huv hcop hvV
      rw [← hpa, ← hpb, ← hpc] at hret
      exact hfree a haA b hbA c hcA hret
    refine Finset.mem_image.mpr ⟨(g, u, v), ?_, ?_⟩
    · apply mem_largeRegularParameters.mpr
      exact ⟨⟨hg, hgN⟩, ⟨hu, huN⟩, ⟨hv, hvN⟩, huv, hVv, hcop,
        hpc ▸ hcN, hpa ▸ hreg a ha, hpb ▸ hreg b hb, hpc ▸ hreg c hc⟩
    · simp only [tripleOfParameters, ← hpa, ← hpb, ← hpc]
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem relaxed_removal_reduction (N V K : ℕ) :
    (relaxedExtremal V N : ℝ) - extremal N ≤
      500000 * Parameters.z ^ (-(K : ℝ)) * N + (largeRegularParameters N V K).card := by
  obtain ⟨A, hA, hfree, hcard⟩ := exists_maximumCard (relaxedFree_empty V) (Finset.Icc 1 N)
  have hfinite := finite_removal_bound A (irregularVertices N K) hA
  have htriple := residual_triples_le_parameters (K := K) A hA hfree
  have hnat : relaxedExtremal V N ≤ extremal N + (irregularVertices N K).card +
      (largeRegularParameters N V K).card := by
    change A.card = relaxedExtremal V N at hcard
    omega
  have hreal : (relaxedExtremal V N : ℝ) ≤ extremal N + (irregularVertices N K).card +
      (largeRegularParameters N V K).card := by exact_mod_cast hnat
  have hex := irregular_card_bound N K
  linarith

theorem removalEstimate_of_largeRegular_bound
    (hcount : ∀ N V K : ℕ, 4 ≤ N → 4 ≤ V →
      ((largeRegularParameters N V K).card : ℝ) ≤
        (N : ℝ) * (10 ^ 23 * Parameters.q ^ (3 * K) *
          (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ))))) :
    RemovalEstimateStatement := by
  intro N V K hN hV
  constructor
  · exact sub_nonneg.mpr (by exact_mod_cast extremal_le_relaxed V N)
  · have h := relaxed_removal_reduction N V K
    rw [Real.rpow_neg_natCast] at h
    have hc := hcount N V K hN hV
    calc
      (relaxedExtremal V N : ℝ) - extremal N ≤
          500000 * Parameters.z ^ (-(K : ℤ)) * N + (largeRegularParameters N V K).card := h
      _ ≤ 500000 * Parameters.z ^ (-(K : ℤ)) * N +
          (N : ℝ) * (10 ^ 23 * Parameters.q ^ (3 * K) *
            (Real.rpow (Real.log V) (-(7 / 80 : ℝ)) + Real.rpow (Real.log N) (-(7 / 80 : ℝ)))) :=
        add_le_add le_rfl hc
      _ = _ := by ring

end Erdos302
