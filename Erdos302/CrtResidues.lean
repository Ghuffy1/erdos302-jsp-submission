import Erdos302.SelbergWeights
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Data.Fintype.BigOperators

namespace Erdos302

noncomputable def pairCrtEquiv {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) :
    (ZMod (∏ i, m i) × ZMod (∏ i, m i)) ≃ (∀ i, ZMod (m i) × ZMod (m i)) := by
  let e := (ZMod.prodEquivPi m hcop).toEquiv
  exact
    { toFun := fun r i => (e r.1 i, e r.2 i)
      invFun := fun f => (e.symm (fun i => (f i).1), e.symm (fun i => (f i).2))
      left_inv := by intro r; simp
      right_inv := by intro f; funext i; simp }

theorem pairCrtEquiv_natCast {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hcop : Pairwise (fun i j => Nat.Coprime (m i) (m j))) (a b : ℕ) (i : ι) :
    pairCrtEquiv m hcop ((a : ZMod (∏ i, m i)), (b : ZMod (∏ i, m i))) i =
      ((a : ZMod (m i)), (b : ZMod (m i))) := by
  simp [pairCrtEquiv, ZMod.prodEquivPi_apply,
    ZMod.cast_natCast (Finset.dvd_prod_of_mem m (Finset.mem_univ i))]

theorem primeFactors_product (q : ℕ) (hq : Squarefree q) :
    (∏ p : q.primeFactors, (p : ℕ)) = q := by
  exact (q.primeFactors.prod_coe_sort (fun p : ℕ => p)).trans
    (Nat.prod_primeFactors_of_squarefree hq)

noncomputable def squarefreePairEquiv (q : ℕ) (hq : Squarefree q) :
    (ZMod q × ZMod q) ≃ (∀ p : q.primeFactors, ZMod (p : ℕ) × ZMod (p : ℕ)) := by
  let e := (ZMod.ringEquivCongr (primeFactors_product q hq).symm).toEquiv
  have hcop : Pairwise (fun p r : q.primeFactors => Nat.Coprime (p : ℕ) (r : ℕ)) := by
    intro p r hpr
    apply (Nat.coprime_primes (Nat.prime_of_mem_primeFactors p.property)
      (Nat.prime_of_mem_primeFactors r.property)).mpr
    intro h
    exact hpr (Subtype.ext h)
  exact (Equiv.prodCongr e e).trans (pairCrtEquiv (fun p : q.primeFactors => (p : ℕ)) hcop)

theorem squarefreePairEquiv_natCast (q : ℕ) (hq : Squarefree q) (a b : ℕ)
    (p : q.primeFactors) :
    squarefreePairEquiv q hq ((a : ZMod q), (b : ZMod q)) p =
      ((a : ZMod (p : ℕ)), (b : ZMod (p : ℕ))) := by
  simp only [squarefreePairEquiv, Equiv.trans_apply, Equiv.prodCongr_apply]
  simp only [RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, Prod.map_apply, map_natCast]
  exact pairCrtEquiv_natCast _ _ a b p

noncomputable def crtResiduePairs (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) : Finset (ZMod q × ZMod q) := by
  classical
  exact (Fintype.piFinset (fun p : q.primeFactors => U p)).map
    (squarefreePairEquiv q hq).symm.toEmbedding

theorem mem_crtResiduePairs (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (r : ZMod q × ZMod q) :
    r ∈ crtResiduePairs q hq U ↔ ∀ p : q.primeFactors, squarefreePairEquiv q hq r p ∈ U p := by
  classical
  unfold crtResiduePairs
  constructor
  · intro hr
    obtain ⟨f, hf, rfl⟩ := Finset.mem_map.mp hr
    simpa only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply] using Fintype.mem_piFinset.mp hf
  · intro hr
    exact Finset.mem_map.mpr ⟨squarefreePairEquiv q hq r, Fintype.mem_piFinset.mpr hr,
      (squarefreePairEquiv q hq).symm_apply_apply r⟩

theorem natCast_mem_crtResiduePairs (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) (a b : ℕ) :
    ((a : ZMod q), (b : ZMod q)) ∈ crtResiduePairs q hq U ↔
      ∀ p ∈ q.primeFactors, ((a : ZMod p), (b : ZMod p)) ∈ U p := by
  rw [mem_crtResiduePairs]
  simp only [squarefreePairEquiv_natCast, Subtype.forall]

theorem card_crtResiduePairs (q : ℕ) (hq : Squarefree q)
    (U : ∀ p : ℕ, Finset (ZMod p × ZMod p)) :
    (crtResiduePairs q hq U).card = ∏ p ∈ q.primeFactors, (U p).card := by
  classical
  simp only [crtResiduePairs, Finset.card_map, Fintype.card_piFinset]
  exact q.primeFactors.prod_coe_sort (fun p : ℕ => (U p).card)

end Erdos302
