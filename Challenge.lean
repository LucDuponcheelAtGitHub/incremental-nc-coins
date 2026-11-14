module

public import Mathlib

@[expose] public section

namespace IncrementalCyclic

open Function (Bijective)
open Nat (mod_lt)
open Finset (univ)

open scoped Finset

def cyclicSquare
    (n : ℕ)
    (p : Fin n → Fin n)
    (h : n ≥ 4)
    (_ : n ≠ 4 ∧ n ≠ 6) :
  Fin n → Fin n → Fin n :=

    fun i j =>
      ⟨(i.val + (p j).val) % n, mod_lt _ (Nat.zero_lt_of_lt h)⟩

def sumDiagOk
    (n : ℕ)
    (s : ℕ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun ij : Fin n × Fin n =>
        ij.1.val + ij.2.val = s
      ∧ (L ij.1 ij.2).val ≤ k

def diffDiagOk
    (n : ℕ)
    (d : ℤ)
    (k : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    univ.filter fun ij : Fin n × Fin n =>
        ((ij.1.val : ℤ) - (ij.2.val : ℤ)) = d
      ∧ (L ij.1 ij.2).val ≤ k

def IsIncremental
    (n : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Prop :=

        (∀ i : Fin n, Bijective (L i .))
      ∧ (∀ j : Fin n, Bijective (L . j))
    ∧ ∀ k : ℕ,
        k < n →
          (∀ s : ℕ, #(sumDiagOk  n s k L) ≤ k + 1)
        ∧ (∀ d : ℤ, #(diffDiagOk n d k L) ≤ k + 1)

def IsNCCoinsSolution
    (n c : ℕ)
    (S : Finset (Fin n × Fin n)) :
  Prop :=

        #S = n * c
      ∧ (∀ i : Fin n, #(S.filter fun ij => ij.1 = i) ≤ c)
      ∧ (∀ j : Fin n, #(S.filter fun ij => ij.2 = j) ≤ c)
      ∧ (∀ s : ℕ, #(S.filter fun ij => ij.1.val + ij.2.val = s) ≤ c)
      ∧ (∀ d : ℤ, #(S.filter fun ij => ((ij.1.val : ℤ) - (ij.2.val : ℤ)) = d) ≤ c)

def coinsFromSquare
    (n c : ℕ)
    (L : Fin n → Fin n → Fin n) :
  Finset (Fin n × Fin n) :=

    if c = 0 then ∅
    else univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val ≤ c - 1

theorem incremental_represents_nc_coins
    (n c : ℕ) (_h : n ≥ 4) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n) (hL : IsIncremental n L) :
    IsNCCoinsSolution n c (coinsFromSquare n c L) := by
  sorry

theorem exists_cyclic_incremental
    (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6) :
    ∃ p : Fin n → Fin n,
          Bijective p
        ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  sorry

theorem exists_incremental_ge_4
    (n : ℕ) (hge : n ≥ 4) :
    ∃ L : Fin n → Fin n → Fin n, IsIncremental n L := by
  sorry

theorem exists_incremental_representing_nc_coins
    (n : ℕ) (hge : n ≥ 4) :
    ∃ L : Fin n → Fin n → Fin n,
          IsIncremental n L
        ∧ ∀ c : ℕ, c ≤ n → IsNCCoinsSolution n c (coinsFromSquare n c L) := by
  sorry

end IncrementalCyclic
