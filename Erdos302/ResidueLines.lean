import Erdos302.PrimeBoxSieve
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Erdos302

inductive ResidueLine
  | leftZero
  | rightZero
  | sumZero
  deriving DecidableEq

instance : Fintype ResidueLine where
  elems := {.leftZero, .rightZero, .sumZero}
  complete := by intro l; cases l <;> simp

theorem card_residueLine : Fintype.card ResidueLine = 3 := by decide

def linePoint (p : ℕ) (l : ResidueLine) (k : Fin p) : ZMod p × ZMod p :=
  match l with
  | .leftZero => (0, ((k : ℕ) : ZMod p))
  | .rightZero => (((k : ℕ) : ZMod p), 0)
  | .sumZero => (((k : ℕ) : ZMod p), -((k : ℕ) : ZMod p))

def lineCondition {p : ℕ} (l : ResidueLine) (r : ZMod p × ZMod p) : Prop :=
  match l with
  | .leftZero => r.1 = 0
  | .rightZero => r.2 = 0
  | .sumZero => r.1 + r.2 = 0

noncomputable def lineResidues (p : ℕ) (l : ResidueLine) : Finset (ZMod p × ZMod p) := by
  classical
  exact Finset.univ.image (linePoint p l)

theorem linePoint_injective (p : ℕ) (l : ResidueLine) : Function.Injective (linePoint p l) := by
  intro a b h
  apply Fin.ext
  cases l with
  | leftZero =>
    have hv := congrArg (fun r : ZMod p × ZMod p => r.2.val) h
    simpa only [linePoint, ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv
  | rightZero =>
    have hv := congrArg (fun r : ZMod p × ZMod p => r.1.val) h
    simpa only [linePoint, ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv
  | sumZero =>
    have hv := congrArg (fun r : ZMod p × ZMod p => r.1.val) h
    simpa only [linePoint, ZMod.val_natCast_of_lt a.isLt, ZMod.val_natCast_of_lt b.isLt] using hv

theorem card_lineResidues (p : ℕ) (l : ResidueLine) : (lineResidues p l).card = p := by
  classical
  rw [lineResidues, Finset.card_image_of_injective _ (linePoint_injective p l)]
  simp

theorem mem_lineResidues {p : ℕ} (hp : 0 < p) (l : ResidueLine) (r : ZMod p × ZMod p) :
    r ∈ lineResidues p l ↔ lineCondition l r := by
  classical
  letI : NeZero p := ⟨hp.ne'⟩
  cases l with
  | leftZero =>
    constructor
    · intro hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      rfl
    · intro hr
      refine Finset.mem_image.mpr ⟨⟨r.2.val, ZMod.val_lt r.2⟩, Finset.mem_univ _, ?_⟩
      ext
      · exact hr.symm
      · exact ZMod.natCast_zmod_val _
  | rightZero =>
    constructor
    · intro hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      rfl
    · intro hr
      refine Finset.mem_image.mpr ⟨⟨r.1.val, ZMod.val_lt r.1⟩, Finset.mem_univ _, ?_⟩
      ext
      · exact ZMod.natCast_zmod_val _
      · exact hr.symm
  | sumZero =>
    constructor
    · intro hr
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hr
      simp [lineCondition, linePoint]
    · intro hr
      refine Finset.mem_image.mpr ⟨⟨r.1.val, ZMod.val_lt r.1⟩, Finset.mem_univ _, ?_⟩
      ext
      · exact ZMod.natCast_zmod_val _
      · change -((r.1.val : ℕ) : ZMod p) = r.2
        rw [ZMod.natCast_zmod_val]
        change r.1 + r.2 = 0 at hr
        linear_combination -hr

noncomputable def selectedResidues (p : ℕ) (s : ResidueLine → Bool) : Finset (ZMod p × ZMod p) := by
  classical
  exact (Finset.univ.filter (fun l => s l = true)).biUnion (lineResidues p)

theorem mem_selectedResidues {p : ℕ} (hp : 0 < p) (s : ResidueLine → Bool) (r : ZMod p × ZMod p) :
    r ∈ selectedResidues p s ↔ ∃ l, s l = true ∧ lineCondition l r := by
  classical
  simp only [selectedResidues, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, mem_lineResidues hp]

theorem card_selectedResidues_le (p : ℕ) (s : ResidueLine → Bool) :
    (selectedResidues p s).card ≤ 3 * p := by
  classical
  have h := Finset.card_biUnion_le (s := Finset.univ.filter (fun l => s l = true)) (t := lineResidues p)
  have hc : (Finset.univ.filter (fun l => s l = true)).card ≤ 3 := by
    simpa only [Finset.card_univ, card_residueLine] using
      Finset.card_le_card (Finset.filter_subset (fun l => s l = true) Finset.univ)
  calc
    (selectedResidues p s).card ≤ ∑ l ∈ Finset.univ.filter (fun l => s l = true), (lineResidues p l).card := h
    _ = (Finset.univ.filter (fun l => s l = true)).card * p := by simp [card_lineResidues]
    _ ≤ 3 * p := Nat.mul_le_mul_right p hc

theorem card_selectedResidues_lt {p : ℕ} (hp : 3 ≤ p) (s : ResidueLine → Bool) :
    (selectedResidues p s).card < p ^ 2 := by
  classical
  letI : NeZero p := ⟨by omega⟩
  have h1 : (1 : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hlt : 1 < p := by omega
    norm_num [ZMod.val_one_eq_one_mod, ZMod.val_zero, Nat.mod_eq_of_lt hlt] at hv
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hv := congrArg ZMod.val h
    have hlt : 2 < p := by omega
    norm_num [ZMod.val_two_eq_two_mod, ZMod.val_zero, Nat.mod_eq_of_lt hlt] at hv
  have hmiss : ((1 : ZMod p), (1 : ZMod p)) ∉ selectedResidues p s := by
    intro h
    obtain ⟨l, hl, hcond⟩ := (mem_selectedResidues (by omega) s _).mp h
    cases l with
    | leftZero => exact h1 hcond
    | rightZero => exact h1 hcond
    | sumZero =>
      apply h2
      change 1 + 1 = 0 at hcond
      norm_num at hcond
      exact hcond
  have hproper : selectedResidues p s ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro h
    apply hmiss
    rw [h]
    exact Finset.mem_univ _
  simpa [pow_two] using Finset.card_lt_card hproper

end Erdos302
