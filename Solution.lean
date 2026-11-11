module

public import IncrementalNCCoins

@[expose] public section

namespace IncrementalCyclic

open Function (Bijective)

theorem incremental_represents_nc_coins
    (n c : ℕ) (_ : n ≥ 4) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n) (hL : IsIncremental n L) :
    IsNCCoinsSolution n c (coinsFromSquare n c L) :=
  ⟨coinsFromSquare_card n c hc L hL.1,
   coinsFromSquare_row_le n c hc L hL.1,
   coinsFromSquare_col_le n c hc L hL.2.1,
   coinsFromSquare_sumDiag_le n c hc L hL.2.2,
   coinsFromSquare_diffDiag_le n c hc L hL.2.2⟩

theorem exists_cyclic_incremental
    (n : ℕ) (hge : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6) :
    ∃ p : Fin n → Fin n,
          Bijective p
        ∧ @IsIncremental n (@cyclicSquare n p hge hn) :=
  Conjecture n hge hn

theorem exists_incremental_ge_4
    (n : ℕ) (hge : n ≥ 4) :
    ∃ L : Fin n → Fin n → Fin n, IsIncremental n L := by
  by_cases h4 : n = 4
  · subst h4
    exact ⟨L4, isIncremental_L4⟩
  · by_cases h6 : n = 6
    · subst h6
      exact ⟨L6, isIncremental_L6⟩
    · obtain ⟨p, _hp_bij, hL⟩ := exists_cyclic_incremental n hge ⟨h4, h6⟩
      exact ⟨@cyclicSquare n p hge ⟨h4, h6⟩, hL⟩

theorem exists_incremental_representing_nc_coins
    (n : ℕ) (hge : n ≥ 4) :
    ∃ L : Fin n → Fin n → Fin n,
          IsIncremental n L
        ∧ ∀ c : ℕ, c ≤ n → IsNCCoinsSolution n c (coinsFromSquare n c L) := by
  obtain ⟨L, hL⟩ := exists_incremental_ge_4 n hge
  exact ⟨L, hL, fun c hc => incremental_represents_nc_coins n c hge hc L hL⟩

end IncrementalCyclic
