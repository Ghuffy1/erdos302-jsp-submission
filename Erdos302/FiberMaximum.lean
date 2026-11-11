import Erdos302.FiberSets

namespace Erdos302

theorem maximumCard_dilate {q : ℕ} (hq : 0 < q) (S : Finset ℕ) :
    maximumCard NoUnitFractionTriple (S.image (fun n => q * n)) =
      maximumCard NoUnitFractionTriple S := by
  classical
  have hinj : Function.Injective (fun n : ℕ => q * n) :=
    fun _ _ h => Nat.eq_of_mul_eq_mul_left hq h
  apply le_antisymm
  · obtain ⟨A, hAS, hfree, hcard⟩ :=
      exists_maximumCard noUnitFractionTriple_empty (S.image (fun n => q * n))
    obtain ⟨B, hBS, hBA⟩ := Finset.subset_image_iff.mp hAS
    have hB : NoUnitFractionTriple B := (noTriple_dilate_iff hq B).mp (hBA ▸ hfree)
    have hc : B.card = A.card := by
      rw [← hBA, Finset.card_image_of_injective _ hinj]
    rw [← hcard, ← hc]
    exact card_le_maximumCard hBS hB
  · obtain ⟨A, hAS, hfree, hcard⟩ := exists_maximumCard noUnitFractionTriple_empty S
    have himage : NoUnitFractionTriple (A.image (fun n => q * n)) :=
      (noTriple_dilate_iff hq A).mpr hfree
    have h := card_le_maximumCard (Finset.image_subset_image hAS) himage
    rw [Finset.card_image_of_injective _ hinj, hcard] at h
    exact h

theorem maximumCard_fiber {P : Finset ℕ} {N q : ℕ} (hq : IsRough P q) :
    maximumCard NoUnitFractionTriple (fiber P N q) = smoothAlpha P (N / q) := by
  rw [fiber_eq_image hq, maximumCard_dilate (Nat.pos_of_ne_zero hq.1)]
  rfl

theorem relaxedExtremal_le_fiber_sum (V N : ℕ) :
    relaxedExtremal V N ≤
      ∑ q ∈ roughIndices (primeSet V) N, smoothAlpha (primeSet V) (N / q) := by
  classical
  obtain ⟨A, hA, hfree, hcard⟩ := exists_maximumCard (relaxedFree_empty V) (Finset.Icc 1 N)
  have hpos : ∀ a ∈ A, 0 < a := fun a ha => (Finset.mem_Icc.mp (hA ha)).1
  have hf := (relaxedFree_iff_fibers hpos).mp hfree
  change maximumCard (RelaxedFree V) (Finset.Icc 1 N) ≤ _
  rw [← hcard, card_eq_sum_rough_fibers hA]
  apply Finset.sum_le_sum
  intro q hq
  have hqR : IsRough (primeSet V) q := (Finset.mem_filter.mp hq).2
  have hsub : A.filter (fun n => roughFactor (primeSet V) n = q) ⊆
      fiber (primeSet V) N q := by
    intro n hn
    obtain ⟨hna, hnq⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hA hna, hnq⟩
  have h := card_le_maximumCard hsub (hf q)
  rwa [maximumCard_fiber hqR] at h

noncomputable def smoothMaxSet (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  Classical.choose (exists_maximumCard noUnitFractionTriple_empty (smoothVertices P M))

theorem smoothMaxSet_spec (P : Finset ℕ) (M : ℕ) :
    smoothMaxSet P M ⊆ smoothVertices P M ∧ NoUnitFractionTriple (smoothMaxSet P M) ∧
      (smoothMaxSet P M).card = smoothAlpha P M :=
  Classical.choose_spec (exists_maximumCard noUnitFractionTriple_empty (smoothVertices P M))

noncomputable def liftedMaxSet (P : Finset ℕ) (N q : ℕ) : Finset ℕ :=
  (smoothMaxSet P (N / q)).image (fun n => q * n)

theorem liftedMaxSet_subset {P : Finset ℕ} {N q : ℕ} (hq : 0 < q) :
    liftedMaxSet P N q ⊆ Finset.Icc 1 N := by
  intro n hn
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hspos, hsN, _⟩ := mem_smoothVertices.mp ((smoothMaxSet_spec P (N / q)).1 hs)
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.mul_pos hq (by omega), ?_⟩
  have h := (Nat.le_div_iff_mul_le hq).mp hsN
  simpa only [mul_comm] using h

theorem liftedMaxSet_rough {P : Finset ℕ} {N q n : ℕ} (hq : IsRough P q)
    (hn : n ∈ liftedMaxSet P N q) : roughFactor P n = q := by
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
  have hsm := (mem_smoothVertices.mp ((smoothMaxSet_spec P (N / q)).1 hs)).2.2
  rw [roughFactor_mul_smooth hq.1 hsm, roughFactor_of_rough hq]

theorem liftedMaxSet_free {P : Finset ℕ} {N q : ℕ} (hq : 0 < q) :
    NoUnitFractionTriple (liftedMaxSet P N q) :=
  (noTriple_dilate_iff hq _).mpr (smoothMaxSet_spec P (N / q)).2.1

theorem liftedMaxSet_card {P : Finset ℕ} {N q : ℕ} (hq : 0 < q) :
    (liftedMaxSet P N q).card = smoothAlpha P (N / q) := by
  rw [liftedMaxSet, Finset.card_image_of_injective _
    (fun _ _ h => Nat.eq_of_mul_eq_mul_left hq h)]
  exact (smoothMaxSet_spec P (N / q)).2.2

theorem liftedMaxSet_pairwise (P : Finset ℕ) (N : ℕ) :
    (roughIndices P N : Set ℕ).PairwiseDisjoint (liftedMaxSet P N) := by
  classical
  intro q hq r hr hqr
  apply Finset.disjoint_left.mpr
  intro n hnq hnr
  have heq := (liftedMaxSet_rough (Finset.mem_filter.mp hq).2 hnq).symm.trans
    (liftedMaxSet_rough (Finset.mem_filter.mp hr).2 hnr)
  exact hqr heq

theorem fiber_sum_le_relaxedExtremal (V N : ℕ) :
    (∑ q ∈ roughIndices (primeSet V) N, smoothAlpha (primeSet V) (N / q)) ≤
      relaxedExtremal V N := by
  classical
  let P := primeSet V
  let A := (roughIndices P N).biUnion (liftedMaxSet P N)
  have hposq : ∀ q ∈ roughIndices P N, 0 < q := fun q hq =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
  have hA : A ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨q, hq, hnq⟩ := Finset.mem_biUnion.mp hn
    exact liftedMaxSet_subset (hposq q hq) hnq
  have hposA : ∀ n ∈ A, 0 < n := fun n hn => (Finset.mem_Icc.mp (hA hn)).1
  have hfree : RelaxedFree V A := by
    apply (relaxedFree_iff_fibers hposA).mpr
    intro q
    by_cases hq : q ∈ roughIndices P N
    · apply noUnitFractionTriple_mono (B := liftedMaxSet P N q) _
        (liftedMaxSet_free (hposq q hq))
      intro n hn
      obtain ⟨hnA, hnq⟩ := Finset.mem_filter.mp hn
      obtain ⟨r, hr, hnr⟩ := Finset.mem_biUnion.mp hnA
      have hnr' := liftedMaxSet_rough (Finset.mem_filter.mp hr).2 hnr
      have heq : r = q := hnr'.symm.trans hnq
      exact heq ▸ hnr
    · have hempty : A.filter (fun n => roughFactor P n = q) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        obtain ⟨hnA, hnq⟩ := Finset.mem_filter.mp hn
        obtain ⟨r, hr, hnr⟩ := Finset.mem_biUnion.mp hnA
        have hnr' := liftedMaxSet_rough (Finset.mem_filter.mp hr).2 hnr
        have heq : r = q := hnr'.symm.trans hnq
        exact hq (heq ▸ hr)
      rw [hempty]
      exact noUnitFractionTriple_empty
  have hcard : A.card = ∑ q ∈ roughIndices P N, smoothAlpha P (N / q) := by
    rw [Finset.card_biUnion (liftedMaxSet_pairwise P N)]
    exact Finset.sum_congr rfl (fun q hq => liftedMaxSet_card (hposq q hq))
  rw [← hcard]
  exact card_le_maximumCard hA hfree

theorem relaxedExtremal_fiber_sum (V N : ℕ) :
    relaxedExtremal V N =
      ∑ q ∈ roughIndices (primeSet V) N, smoothAlpha (primeSet V) (N / q) :=
  le_antisymm (relaxedExtremal_le_fiber_sum V N) (fiber_sum_le_relaxedExtremal V N)

end Erdos302
