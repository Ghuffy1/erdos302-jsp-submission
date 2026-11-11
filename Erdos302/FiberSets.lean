import Erdos302.FiberEdges

namespace Erdos302

def fiber (P : Finset ℕ) (N q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => roughFactor P n = q)

noncomputable def roughIndices (P : Finset ℕ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (IsRough P)

theorem roughFactor_mem_indices {P : Finset ℕ} {N n : ℕ}
    (hn : n ∈ Finset.Icc 1 N) : roughFactor P n ∈ roughIndices P N := by
  classical
  have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
  have hqpos := Nat.pos_of_ne_zero (roughFactor_ne_zero P n)
  have hqle := Nat.le_of_dvd hnpos (roughFactor_dvd P hnpos.ne')
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hqpos, hqle.trans (Finset.mem_Icc.mp hn).2⟩,
    roughFactor_isRough P n⟩

theorem fiber_eq_image {P : Finset ℕ} {N q : ℕ} (hq : IsRough P q) :
    fiber P N q = (smoothVertices P (N / q)).image (fun s => q * s) := by
  classical
  have hqpos := Nat.pos_of_ne_zero hq.1
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hnq⟩ := Finset.mem_filter.mp hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Icc.mp hnI
    have hn0 : n ≠ 0 := by omega
    have hspos := Nat.pos_of_ne_zero (smoothFactor_ne_zero P n)
    have hprod : q * smoothFactor P n = n := by
      rw [← hnq]
      exact roughFactor_mul_smoothFactor hn0
    have hsN : smoothFactor P n ≤ N / q := by
      apply (Nat.le_div_iff_mul_le hqpos).mpr
      simpa only [mul_comm, hprod] using hnN
    exact Finset.mem_image.mpr ⟨smoothFactor P n,
      mem_smoothVertices.mpr ⟨hspos, hsN, smoothFactor_mem P n⟩, hprod⟩
  · intro hn
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hspos, hsN, hsmooth⟩ := mem_smoothVertices.mp hs
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hqpos (by omega), ?_⟩, ?_⟩
    · have h := (Nat.le_div_iff_mul_le hqpos).mp hsN
      simpa only [mul_comm] using h
    · rw [roughFactor_mul_smooth hq.1 hsmooth, roughFactor_of_rough hq]

theorem fiber_card {P : Finset ℕ} {N q : ℕ} (hq : IsRough P q) :
    (fiber P N q).card = (smoothVertices P (N / q)).card := by
  classical
  rw [fiber_eq_image hq]
  apply Finset.card_image_of_injective
  intro s t h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq.1) h

theorem card_eq_sum_rough_fibers {P : Finset ℕ} {N : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.Icc 1 N) :
    A.card = ∑ q ∈ roughIndices P N, (A.filter (fun n => roughFactor P n = q)).card := by
  classical
  exact Finset.card_eq_sum_card_fiberwise (fun n hn => roughFactor_mem_indices (hA hn))

theorem reciprocalEquation_dilate_iff {q a b c : ℕ} (hq : 0 < q) :
    ReciprocalEquation (q * a) (q * b) (q * c) ↔ ReciprocalEquation a b c := by
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [ReciprocalEquation, Nat.cast_mul, one_div, mul_inv_rev]
  rw [← add_mul]
  constructor
  · intro h
    exact mul_right_cancel₀ (inv_ne_zero hq') h
  · intro h
    exact congrArg (fun x : ℚ => x * (q : ℚ)⁻¹) h

theorem noTriple_dilate_iff {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    NoUnitFractionTriple (A.image (fun n => q * n)) ↔ NoUnitFractionTriple A := by
  classical
  constructor
  · intro h a ha b hb c hc hab hac hbc heq
    apply h (q * a) (Finset.mem_image_of_mem _ ha)
      (q * b) (Finset.mem_image_of_mem _ hb) (q * c) (Finset.mem_image_of_mem _ hc)
    · exact fun he => hab (Nat.eq_of_mul_eq_mul_left hq he)
    · exact fun he => hac (Nat.eq_of_mul_eq_mul_left hq he)
    · exact fun he => hbc (Nat.eq_of_mul_eq_mul_left hq he)
    · exact reciprocalEquation_dilate_iff hq |>.mpr heq
  · intro h a ha b hb c hc hab hac hbc heq
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hc
    apply h a₀ ha₀ b₀ hb₀ c₀ hc₀
    · exact fun he => hab (congrArg (q * ·) he)
    · exact fun he => hac (congrArg (q * ·) he)
    · exact fun he => hbc (congrArg (q * ·) he)
    · exact reciprocalEquation_dilate_iff hq |>.mp heq

end Erdos302
