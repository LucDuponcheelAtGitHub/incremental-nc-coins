module

public import Mathlib

public import IncrementalNCCoins.Basic

@[expose] public section

namespace IncrementalCyclic

open Function (Bijective)
open Nat (mod_lt)
open Finset (univ)

open scoped Finset

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
