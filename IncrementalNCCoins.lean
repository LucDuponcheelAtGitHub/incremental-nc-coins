module

public import IncrementalNCCoins.Basic

@[expose] public section

namespace IncrementalCyclic

open Function (Bijective)
open Nat (mod_lt)
open Finset (univ)

open scoped Finset

lemma coinsFromSquare_eq_filter_lt
    (n c : ℕ)
    (L : Fin n → Fin n → Fin n) :
    coinsFromSquare n c L = univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val < c := by
  unfold coinsFromSquare
  split_ifs with hc0
  · subst hc0
    ext ij
    simp
  · ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega

lemma card_filter_le_of_bijective
    {n k : ℕ} (hk : k < n) (f : Fin n → Fin n) (hf : Bijective f) :
    #(univ.filter fun x : Fin n => (f x).val ≤ k) = k + 1 := by
  have hbij : #(univ.filter fun x : Fin n => (f x).val ≤ k) = #(Finset.range (k + 1)) := by
    apply Finset.card_bij (fun x _ => (f x).val)
    · intro x hx
      rw [Finset.mem_filter] at hx
      exact Finset.mem_range.mpr (by omega)
    · intro x₁ _ x₂ _ heq
      exact hf.injective (Fin.ext heq)
    · intro y hy
      rw [Finset.mem_range] at hy
      obtain ⟨x, hx⟩ := hf.surjective ⟨y, by omega⟩
      refine ⟨x, ?_, congrArg Fin.val hx⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, by rw [hx]; dsimp only; omega⟩
  rw [hbij, Finset.card_range]

lemma coinsFromSquare_row_card
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hrow_bij : ∀ i : Fin n, Bijective (L i .))
    (i : Fin n) :
    #((coinsFromSquare n c L).filter fun ij => ij.1 = i) = c := by
  unfold coinsFromSquare
  split_ifs with hc0
  · subst hc0
    simp
  · have hcard : #((univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val ≤ c - 1).filter
        fun ij => ij.1 = i) =
        #(univ.filter fun j : Fin n => (L i j).val ≤ c - 1) := by
      apply Finset.card_bij (fun ij _ => ij.2)
      · intro ij hij
        rw [Finset.mem_filter, Finset.mem_filter] at hij
        rcases hij with ⟨⟨_, hle⟩, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩
      · intro ij₁ hij₁ ij₂ hij₂ heq
        rw [Finset.mem_filter] at hij₁ hij₂
        exact Prod.ext (hij₁.2.trans hij₂.2.symm) heq
      · intro j hj
        rw [Finset.mem_filter] at hj
        refine ⟨(i, j), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, hj.2⟩, rfl⟩
    rw [hcard, card_filter_le_of_bijective (by omega) (L i .) (hrow_bij i)]
    omega

lemma coinsFromSquare_card
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hrow_bij : ∀ i : Fin n, Bijective (L i .)) :
    #(coinsFromSquare n c L) = n * c := by
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) (fun _ _ => Finset.mem_univ _)]
  simp [coinsFromSquare_row_card n c hc L hrow_bij]

lemma coinsFromSquare_row_le
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hrow_bij : ∀ i : Fin n, Bijective (L i .)) :
    ∀ i : Fin n, #((coinsFromSquare n c L).filter fun ij => ij.1 = i) ≤ c :=
  fun i => (coinsFromSquare_row_card n c hc L hrow_bij i).le

lemma coinsFromSquare_col_le
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hcol_bij : ∀ j : Fin n, Bijective (L . j)) :
    ∀ j : Fin n, #((coinsFromSquare n c L).filter fun ij => ij.2 = j) ≤ c := by
  intro j
  unfold coinsFromSquare
  split_ifs with hc0
  · subst hc0
    simp
  · have hcard : #((univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val ≤ c - 1).filter
        fun ij => ij.2 = j) =
        #(univ.filter fun i : Fin n => (L i j).val ≤ c - 1) := by
      apply Finset.card_bij (fun ij _ => ij.1)
      · intro ij hij
        rw [Finset.mem_filter, Finset.mem_filter] at hij
        rw [Finset.mem_filter]
        rcases hij with ⟨⟨_, hle⟩, rfl⟩
        exact ⟨Finset.mem_univ _, hle⟩
      · intro ij₁ hij₁ ij₂ hij₂ heq
        rw [Finset.mem_filter] at hij₁ hij₂
        exact Prod.ext heq (hij₁.2.trans hij₂.2.symm)
      · intro i hi
        rw [Finset.mem_filter] at hi
        refine ⟨(i, j), ?_, rfl⟩
        rw [Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, hi.2⟩, rfl⟩
    rw [hcard, card_filter_le_of_bijective (by omega) (L . j) (hcol_bij j)]
    omega

lemma coinsFromSquare_sumDiag_le
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hdiag : ∀ k : ℕ, k < n →
      (∀ s : ℕ, #(sumDiagOk n s k L) ≤ k + 1) ∧ (∀ d : ℤ, #(diffDiagOk n d k L) ≤ k + 1)) :
    ∀ s : ℕ, #((coinsFromSquare n c L).filter fun ij => ij.1.val + ij.2.val = s) ≤ c := by
  intro s
  unfold coinsFromSquare
  split_ifs with hc0
  · subst hc0
    simp
  · have heq : ((univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val ≤ c - 1).filter
        fun ij => ij.1.val + ij.2.val = s) =
        sumDiagOk n s (c - 1) L := by
      ext ij
      simp only [Finset.mem_filter, sumDiagOk, Finset.mem_univ, true_and, and_comm]
    rw [heq]
    have hle := (hdiag (c - 1) (by omega)).1 s
    omega

lemma coinsFromSquare_diffDiag_le
    (n c : ℕ) (hc : c ≤ n)
    (L : Fin n → Fin n → Fin n)
    (hdiag : ∀ k : ℕ, k < n →
      (∀ s : ℕ, #(sumDiagOk n s k L) ≤ k + 1) ∧ (∀ d : ℤ, #(diffDiagOk n d k L) ≤ k + 1)) :
    ∀ d : ℤ, #((coinsFromSquare n c L).filter fun ij =>
      ((ij.1.val : ℤ) - (ij.2.val : ℤ)) = d) ≤ c := by
  intro d
  unfold coinsFromSquare
  split_ifs with hc0
  · subst hc0
    simp
  · have heq : ((univ.filter fun ij : Fin n × Fin n => (L ij.1 ij.2).val ≤ c - 1).filter
        fun ij => ((ij.1.val : ℤ) - (ij.2.val : ℤ)) = d) =
        diffDiagOk n d (c - 1) L := by
      ext ij
      simp only [Finset.mem_filter, diffDiagOk, Finset.mem_univ, true_and, and_comm]
    rw [heq]
    have hle := (hdiag (c - 1) (by omega)).2 d
    omega

def val_nat (n : ℕ) (p_nat : ℕ → ℕ) (i j : ℕ) : ℕ :=
  if i + p_nat j < n then i + p_nat j else i + p_nat j - n

lemma mod_eq_val_nat (n : ℕ) (p_nat : ℕ → ℕ) (i j : ℕ) (hi : i < n) (hp : p_nat j < n) :
    (i + p_nat j) % n = val_nat n p_nat i j := by
  dsimp only [val_nat]
  split_ifs with hlt
  · exact Nat.mod_eq_of_lt hlt
  · have h1 : n ≤ i + p_nat j := by omega
    have h2 : i + p_nat j - n < n := by omega
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt h2]

lemma val_nat_prop (n : ℕ) (p_nat : ℕ → ℕ) (i j : ℕ) :
    (i + p_nat j < n ∧ val_nat n p_nat i j = i + p_nat j) ∨
    (i + p_nat j ≥ n ∧ val_nat n p_nat i j = i + p_nat j - n) := by
  dsimp only [val_nat]; split_ifs <;> omega

lemma exists_incremental_of_nat
    (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (p_nat : ℕ → ℕ)
    (f_sum f_diff : ℕ → ℕ → ℕ)
    (hp_lt : ∀ j < n, p_nat j < n)
    (hp_inj : ∀ j₁ < n, ∀ j₂ < n, p_nat j₁ = p_nat j₂ → j₁ = j₂)
    (h_sum_le : ∀ i < n, ∀ j < n, f_sum i j ≤ val_nat n p_nat i j)
    (h_diff_le : ∀ i < n, ∀ j < n, f_diff i j ≤ val_nat n p_nat i j)
    (h_sum_inj : ∀ i₁ < n, ∀ j₁ < n, ∀ i₂ < n, ∀ j₂ < n,
      i₁ + j₁ = i₂ + j₂ → f_sum i₁ j₁ = f_sum i₂ j₂ → j₁ = j₂)
    (h_diff_inj : ∀ i₁ < n, ∀ j₁ < n, ∀ i₂ < n, ∀ j₂ < n,
      (i₁ : ℤ) - j₁ = (i₂ : ℤ) - j₂ → f_diff i₁ j₁ = f_diff i₂ j₂ → j₁ = j₂) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  let p : Fin n → Fin n := fun j => ⟨p_nat j.val, hp_lt j.val j.isLt⟩
  have hp_bij : Bijective p := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun j₁ j₂ heq => ?_, rfl⟩
    apply Fin.ext
    exact hp_inj j₁.val j₁.isLt j₂.val j₂.isLt (congrArg Fin.val heq)
  have hL_val : ∀ i j : Fin n, (cyclicSquare n p h hn i j).val
         = val_nat n p_nat i.val j.val := by
    intro i j
    exact mod_eq_val_nat n p_nat i.val j.val i.isLt (hp_lt j.val j.isLt)
  refine ⟨p, hp_bij, ?_, ?_, ?_⟩
  · intro i
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun j₁ j₂ heq => ?_, rfl⟩
    have hval : val_nat n p_nat i.val j₁.val = val_nat n p_nat i.val j₂.val := by
      have h1 := congrArg Fin.val heq
      dsimp only at h1
      rw [hL_val i j₁, hL_val i j₂] at h1
      exact h1
    have hp1 := hp_lt j₁.val j₁.isLt
    have hp2 := hp_lt j₂.val j₂.isLt
    have hv1 := val_nat_prop n p_nat i.val j₁.val
    have hv2 := val_nat_prop n p_nat i.val j₂.val
    have hp_eq : p_nat j₁.val = p_nat j₂.val := by omega
    exact Fin.ext (hp_inj j₁.val j₁.isLt j₂.val j₂.isLt hp_eq)
  · intro j
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun i₁ i₂ heq => ?_, rfl⟩
    have hval : val_nat n p_nat i₁.val j.val = val_nat n p_nat i₂.val j.val := by
      have h1 := congrArg Fin.val heq
      dsimp only at h1
      rw [hL_val i₁ j, hL_val i₂ j] at h1
      exact h1
    have hi1 := i₁.isLt
    have hi2 := i₂.isLt
    have hp1 := hp_lt j.val j.isLt
    have hv1 := val_nat_prop n p_nat i₁.val j.val
    have hv2 := val_nat_prop n p_nat i₂.val j.val
    apply Fin.ext
    omega
  · intro k _hk
    refine ⟨fun s => ?_, fun d => ?_⟩
    · calc #(sumDiagOk n s k (cyclicSquare n p h hn))
        _ ≤ #(Finset.range (k + 1)) := by
          apply Finset.card_le_card_of_injOn (fun ij : Fin n × Fin n => f_sum ij.1.val ij.2.val)
          · intro ij hij
            rw [Finset.mem_coe, sumDiagOk, Finset.mem_filter] at hij
            rw [Finset.mem_coe, Finset.mem_range]
            dsimp only
            have hle := h_sum_le ij.1.val ij.1.isLt ij.2.val ij.2.isLt
            have hval := hL_val ij.1 ij.2
            omega
          · intro ij₁ hij₁ ij₂ hij₂ hfeq
            rw [Finset.mem_coe, sumDiagOk, Finset.mem_filter] at hij₁ hij₂
            have hj : ij₁.2.val = ij₂.2.val :=
              h_sum_inj ij₁.1.val ij₁.1.isLt ij₁.2.val ij₁.2.isLt
                ij₂.1.val ij₂.1.isLt ij₂.2.val ij₂.2.isLt
                (by omega) hfeq
            have hi : ij₁.1.val = ij₂.1.val := by omega
            exact Prod.ext (Fin.ext hi) (Fin.ext hj)
        _ = k + 1 := Finset.card_range (k + 1)
    · calc #(diffDiagOk n d k (cyclicSquare n p h hn))
        _ ≤ #(Finset.range (k + 1)) := by
          apply Finset.card_le_card_of_injOn (fun ij : Fin n × Fin n => f_diff ij.1.val ij.2.val)
          · intro ij hij
            rw [Finset.mem_coe, diffDiagOk, Finset.mem_filter] at hij
            rw [Finset.mem_coe, Finset.mem_range]
            dsimp only
            have hle := h_diff_le ij.1.val ij.1.isLt ij.2.val ij.2.isLt
            have hval := hL_val ij.1 ij.2
            omega
          · intro ij₁ hij₁ ij₂ hij₂ hfeq
            rw [Finset.mem_coe, diffDiagOk, Finset.mem_filter] at hij₁ hij₂
            have hj : ij₁.2.val = ij₂.2.val :=
              h_diff_inj ij₁.1.val ij₁.1.isLt ij₁.2.val ij₁.2.isLt
                ij₂.1.val ij₂.1.isLt ij₂.2.val ij₂.2.isLt
                (by omega) hfeq
            have hi : ij₁.1.val = ij₂.1.val := by omega
            exact Prod.ext (Fin.ext hi) (Fin.ext hj)
        _ = k + 1 := Finset.card_range (k + 1)

def p1_nat (n j : ℕ) : ℕ :=
  if j = 0 then 0
  else if 2 * j < n then n - 2 * j
  else 2 * n - 2 * j

lemma p1_nat_prop (n j : ℕ) :
    (j = 0 ∧ p1_nat n j = 0) ∨
    (j > 0 ∧ 2 * j < n ∧ p1_nat n j = n - 2 * j) ∨
    (j > 0 ∧ 2 * j ≥ n ∧ p1_nat n j = 2 * n - 2 * j) := by
  dsimp only [p1_nat]; split_ifs <;> omega

lemma solve_family1 (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 1 ∨ n % 6 = 5) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  apply exists_incremental_of_nat n h hn
    (p1_nat n) (val_nat n (p1_nat n)) (val_nat n (p1_nat n))
  · intro j hj; have := p1_nat_prop n j; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    have := p1_nat_prop n j₁; have := p1_nat_prop n j₂; omega
  · intro i _ j _; exact le_rfl
  · intro i _ j _; exact le_rfl
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    have := p1_nat_prop n j₁; have := p1_nat_prop n j₂
    have := val_nat_prop n (p1_nat n) i₁ j₁; have := val_nat_prop n (p1_nat n) i₂ j₂
    omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    have := p1_nat_prop n j₁; have := p1_nat_prop n j₂
    have := val_nat_prop n (p1_nat n) i₁ j₁; have := val_nat_prop n (p1_nat n) i₂ j₂
    omega

def p2_nat (n j : ℕ) : ℕ :=
  let m := n / 2
  if j < m then
    if 2 * j + m + 1 < n then
      2 * j + m + 1 else
      2 * j + m + 1 - n
  else
    if 2 * (j - m) + m + 4 < n then
      2 * (j - m) + m + 4 else
      2 * (j - m) + m + 4 - n

lemma p2_nat_lt (n j : ℕ) (hj : j < n / 2) :
    (2 * j + n / 2 + 1 < n ∧ p2_nat n j = 2 * j + n / 2 + 1) ∨
    (2 * j + n / 2 + 1 ≥ n ∧ p2_nat n j = 2 * j + n / 2 + 1 - n) := by
  dsimp only [p2_nat]; split_ifs <;> omega

lemma p2_nat_ge (n j : ℕ) (hj : ¬ j < n / 2) :
    (2 * (j - n / 2) + n / 2 + 4 < n ∧ p2_nat n j = 2 * (j - n / 2) + n / 2 + 4) ∨
    (2 * (j - n / 2) + n / 2 + 4 ≥ n ∧ p2_nat n j = 2 * (j - n / 2) + n / 2 + 4 - n) := by
  dsimp only [p2_nat]; split_ifs <;> omega

def f2_sum (n i j : ℕ) : ℕ :=
  if i < 3 ∧ j ≥ n - 3 then j - (n - 3) else val_nat n (p2_nat n) i j

def f2_diff (n i j : ℕ) : ℕ :=
  if i = n - 1 ∧ j = n - 1 then 1 else val_nat n (p2_nat n) i j

lemma f2_sum_lt_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_sum n i j ≤ val_nat n (p2_nat n) i j ∧ f2_sum n i j < n ∧
    (f2_sum n i j = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hp := p2_nat_lt n j hj
  have hv := val_nat_prop n (p2_nat n) i j
  have hf : f2_sum n i j = val_nat n (p2_nat n) i j := by
    dsimp only [f2_sum]; split_ifs <;> omega
  omega

lemma f2_sum_ge_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_sum n i j ≤ val_nat n (p2_nat n) i j ∧ f2_sum n i j < n ∧
    ((i < 3 ∧ j ≥ n - 3 ∧ f2_sum n i j = j - (n - 3)) ∨
     ((i ≥ 3 ∨ j < n - 3) ∧
      (f2_sum n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_sum n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hp := p2_nat_ge n j hjge
  have hv := val_nat_prop n (p2_nat n) i j
  dsimp only [f2_sum]; split_ifs <;> omega

lemma f2_diff_lt_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n / 2) :
    f2_diff n i j ≤ val_nat n (p2_nat n) i j ∧ f2_diff n i j < n ∧
    (f2_diff n i j = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + n = i + 2 * j + n / 2 + 1 ∨
     f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 1) := by
  have hp := p2_nat_lt n j hj
  have hv := val_nat_prop n (p2_nat n) i j
  have hf : f2_diff n i j = val_nat n (p2_nat n) i j := by
    dsimp only [f2_diff]; split_ifs <;> omega
  omega

lemma f2_diff_ge_prop (n i j : ℕ) (hge : n ≥ 10) (heven : n % 2 = 0) (hi : i < n) (hj : j < n) (hjge : ¬ j < n / 2) :
    f2_diff n i j ≤ val_nat n (p2_nat n) i j ∧ f2_diff n i j < n ∧
    ((i = n - 1 ∧ j = n - 1 ∧ f2_diff n i j = 1) ∨
     (i + j < 2 * n - 2 ∧
      (f2_diff n i j + n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 2 * n = i + 2 * j + n / 2 + 4 ∨
       f2_diff n i j + 3 * n = i + 2 * j + n / 2 + 4))) := by
  have hp := p2_nat_ge n j hjge
  have hv := val_nat_prop n (p2_nat n) i j
  dsimp only [f2_diff]; split_ifs <;> omega

lemma solve_family2 (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 2 ∨ n % 6 = 4) (hge : n ≥ 10) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  have heven : n % 2 = 0 := by omega
  apply exists_incremental_of_nat n h hn
    (p2_nat n) (f2_sum n) (f2_diff n)
  · intro j hj
    by_cases h1 : j < n / 2
    · have := p2_nat_lt n j h1; omega
    · have := p2_nat_ge n j h1; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := p2_nat_lt n j₁ h1; have := p2_nat_lt n j₂ h2; omega
    · have := p2_nat_lt n j₁ h1; have := p2_nat_ge n j₂ h2; omega
    · have := p2_nat_ge n j₁ h1; have := p2_nat_lt n j₂ h2; omega
    · have := p2_nat_ge n j₁ h1; have := p2_nat_ge n j₂ h2; omega
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_sum_lt_prop n i j hge heven hi h1).1
    · exact (f2_sum_ge_prop n i j hge heven hi hj h1).1
  · intro i hi j hj
    by_cases h1 : j < n / 2
    · exact (f2_diff_lt_prop n i j hge heven hi h1).1
    · exact (f2_diff_ge_prop n i j hge heven hi hj h1).1
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_sum_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_sum_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_sum_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_sum_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_sum_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1 : j₁ < n / 2 <;> by_cases h2 : j₂ < n / 2
    · have := f2_diff_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_lt_prop n i₁ j₁ hge heven hi₁ h1
      have := f2_diff_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega
    · have := f2_diff_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_lt_prop n i₂ j₂ hge heven hi₂ h2; omega
    · have := f2_diff_ge_prop n i₁ j₁ hge heven hi₁ hj₁ h1
      have := f2_diff_ge_prop n i₂ j₂ hge heven hi₂ hj₂ h2; omega

def p3_nat (n j : ℕ) : ℕ :=
  let k := n / 3
  if j < k then
    if 3 * j + 2 * k < n then 3 * j + 2 * k else 3 * j + 2 * k - n
  else if j < 2 * k then
    if 3 * (j - k) + 2 * k + 4 < n then 3 * (j - k) + 2 * k + 4 else 3 * (j - k) + 2 * k + 4 - n
  else
    if 3 * (j - 2 * k) + 2 * k + 8 < n then 3 * (j - 2 * k) + 2 * k + 8
    else 3 * (j - 2 * k) + 2 * k + 8 - n

lemma p3_nat_0 (n j : ℕ) (hj : j < n / 3) :
    (3 * j + 2 * (n / 3) < n ∧ p3_nat n j = 3 * j + 2 * (n / 3)) ∨
    (3 * j + 2 * (n / 3) ≥ n ∧ p3_nat n j = 3 * j + 2 * (n / 3) - n) := by
  dsimp only [p3_nat]; split_ifs <;> omega

lemma p3_nat_1 (n j : ℕ) (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    (3 * (j - n / 3) + 2 * (n / 3) + 4 < n ∧ p3_nat n j = 3 * (j - n / 3) + 2 * (n / 3) + 4) ∨
    (3 * (j - n / 3) + 2 * (n / 3) + 4 ≥ n ∧ p3_nat n j = 3 * (j - n / 3) + 2 * (n / 3) + 4 - n) := by
  dsimp only [p3_nat]; split_ifs <;> omega

lemma p3_nat_2 (n j : ℕ) (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    (3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 < n ∧ p3_nat n j = 3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8) ∨
    (3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 ≥ n ∧ p3_nat n j = 3 * (j - 2 * (n / 3)) + 2 * (n / 3) + 8 - n) := by
  dsimp only [p3_nat]; split_ifs <;> omega

def f3_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (p3_nat n) i j
  let k := n / 3
  if i < 4 ∧ (j = n - 4 ∨ j = n - 3) then v - k
  else if i < 4 ∧ (j = n - 2 ∨ j = n - 1) then v - 2 * k
  else v

def f3_diff (n i j : ℕ) : ℕ :=
  let v := val_nat n (p3_nat n) i j
  let k := n / 3
  if i ≥ n - 2 ∧ j = n - 2 then v - 2 * k
  else if i ≥ n - 2 ∧ j = n - 1 then v - k
  else v

lemma f3_sum_0_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f3_sum n i j < n ∧
    (f3_sum n i j = i + 3 * j + 2 * (n / 3) ∨
     f3_sum n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f3_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hp := p3_nat_0 n j hj
  have hv := val_nat_prop n (p3_nat n) i j
  have hf : f3_sum n i j = val_nat n (p3_nat n) i j := by
    dsimp only [f3_sum]; split_ifs <;> omega
  omega

lemma f3_sum_1_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f3_sum n i j < n ∧
    (f3_sum n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f3_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f3_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hp := p3_nat_1 n j hj1 hj2
  have hv := val_nat_prop n (p3_nat n) i j
  have hf : f3_sum n i j = val_nat n (p3_nat n) i j := by
    dsimp only [f3_sum]; split_ifs <;> omega
  omega

lemma f3_sum_2_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f3_sum n i j < n ∧
    ((i < 4 ∧ (j = n - 4 ∨ j = n - 3) ∧ f3_sum n i j + 3 * n = i + 3 * j + n / 3 + 8) ∨
     (i < 4 ∧ (j = n - 2 ∨ j = n - 1) ∧ f3_sum n i j + 3 * n = i + 3 * j + 8) ∨
     ((i ≥ 4 ∨ j < n - 4) ∧
      (f3_sum n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f3_sum n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f3_sum n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hp := p3_nat_2 n j hj1 hj2
  have hv := val_nat_prop n (p3_nat n) i j
  dsimp only [f3_sum]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma f3_diff_0_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n / 3) :
    f3_diff n i j < n ∧
    (f3_diff n i j = i + 3 * j + 2 * (n / 3) ∨
     f3_diff n i j + n = i + 3 * j + 2 * (n / 3) ∨
     f3_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3)) := by
  have hp := p3_nat_0 n j hj
  have hv := val_nat_prop n (p3_nat n) i j
  have hf : f3_diff n i j = val_nat n (p3_nat n) i j := by
    dsimp only [f3_diff]; split_ifs <;> omega
  omega

lemma f3_diff_1_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n)
    (hj1 : ¬ j < n / 3) (hj2 : j < 2 * (n / 3)) :
    f3_diff n i j < n ∧
    (f3_diff n i j + n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f3_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 4 ∨
     f3_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 4) := by
  have hp := p3_nat_1 n j hj1 hj2
  have hv := val_nat_prop n (p3_nat n) i j
  have hf : f3_diff n i j = val_nat n (p3_nat n) i j := by
    dsimp only [f3_diff]; split_ifs <;> omega
  omega

lemma f3_diff_2_prop (n i j : ℕ) (hmod : n % 6 = 3) (hge : n ≥ 27) (hi : i < n) (hj : j < n)
    (hj1 : ¬ j < n / 3) (hj2 : ¬ j < 2 * (n / 3)) :
    f3_diff n i j < n ∧
    ((i ≥ n - 2 ∧ j = n - 2 ∧ f3_diff n i j + n = i + 2) ∨
     (i ≥ n - 2 ∧ j = n - 1 ∧ f3_diff n i j + 2 * (n / 3) = i + 5) ∨
     ((i < n - 2 ∨ j < n - 2) ∧
      (f3_diff n i j + 2 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f3_diff n i j + 3 * n = i + 3 * j + 2 * (n / 3) + 8 ∨
       f3_diff n i j + 4 * n = i + 3 * j + 2 * (n / 3) + 8))) := by
  have hp := p3_nat_2 n j hj1 hj2
  have hv := val_nat_prop n (p3_nat n) i j
  dsimp only [f3_diff]
  split_ifs with h1 h2
  · refine ⟨by omega, Or.inl ⟨h1.1, h1.2, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h2.1, h2.2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

lemma solve_family3 (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 3) (hge : n ≥ 27) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  apply exists_incremental_of_nat n h hn
    (p3_nat n) (f3_sum n) (f3_diff n)
  · intro j hj
    by_cases h1 : j < n / 3
    · have := p3_nat_0 n j h1; omega
    · by_cases h2 : j < 2 * (n / 3)
      · have := p3_nat_1 n j h1 h2; omega
      · have := p3_nat_2 n j h1 h2; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := p3_nat_0 n j₁ h1a; have := p3_nat_0 n j₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := p3_nat_0 n j₁ h1a; have := p3_nat_1 n j₂ h2a h2b; omega
      · have := p3_nat_0 n j₁ h1a; have := p3_nat_2 n j₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := p3_nat_1 n j₁ h1a h1b; have := p3_nat_0 n j₂ h2a; omega
      · have := p3_nat_2 n j₁ h1a h1b; have := p3_nat_0 n j₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := p3_nat_1 n j₁ h1a h1b; have := p3_nat_1 n j₂ h2a h2b; omega
      · have := p3_nat_1 n j₁ h1a h1b; have := p3_nat_2 n j₂ h2a h2b; omega
      · have := p3_nat_2 n j₁ h1a h1b; have := p3_nat_1 n j₂ h2a h2b; omega
      · have := p3_nat_2 n j₁ h1a h1b; have := p3_nat_2 n j₂ h2a h2b; omega
  · intro i _ j _; dsimp only [f3_sum]; split_ifs <;> omega
  · intro i _ j _; dsimp only [f3_diff]; split_ifs <;> omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 3 <;> by_cases h2a : j₂ < n / 3
    · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < 2 * (n / 3)
      · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
    · by_cases h1b : j₁ < 2 * (n / 3)
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < 2 * (n / 3) <;> by_cases h2b : j₂ < 2 * (n / 3)
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f3_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1a h1b
        have := f3_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2a h2b; omega

def p4_nat (n j : ℕ) : ℕ :=
  let m := n / 2
  if j = 0 then n - 2
  else if j < m - 2 then 2 * j + 2
  else if j = m - 2 then 0
  else if j < n - 1 then 2 * (j - (m - 1)) + 1
  else 2

lemma p4_nat_lt (n j : ℕ) (hj : j < n / 2 - 1) :
    (j = 0 ∧ p4_nat n j = n - 2) ∨
    (1 ≤ j ∧ j < n / 2 - 2 ∧ p4_nat n j = 2 * j + 2) ∨
    (j = n / 2 - 2 ∧ p4_nat n j = 0) := by
  dsimp only [p4_nat]
  split_ifs with h1 h2 h3
  · exact Or.inl ⟨h1, rfl⟩
  · exact Or.inr (Or.inl ⟨by omega, h2, rfl⟩)
  · exact Or.inr (Or.inr ⟨h3, rfl⟩)
  · omega
  · omega

lemma p4_nat_ge (n j : ℕ) (hge : n ≥ 12) (hj : ¬ j < n / 2 - 1) (hjlt : j < n) :
    (n / 2 - 1 ≤ j ∧ j < n - 1 ∧ p4_nat n j = 2 * (j - (n / 2 - 1)) + 1) ∨
    (j = n - 1 ∧ p4_nat n j = 2) := by
  dsimp only [p4_nat]
  split_ifs with h1 h2 h3 h4
  · omega
  · omega
  · omega
  · exact Or.inl ⟨by omega, h4, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

def f4_sum (n i j : ℕ) : ℕ :=
  let v := val_nat n (p4_nat n) i j
  let m := n / 2
  if j = m - 1 ∧ i < n - 1 then v - 1
  else if j = n - 5 ∧ i + j < n then v - (m - 2)
  else if j = n - 1 ∧ i < 2 then v - 1
  else v

def f4_diff (n i j : ℕ) : ℕ :=
  let v := val_nat n (p4_nat n) i j
  let m := n / 2
  let k := n / 3
  if 1 + k ≤ j ∧ j ≤ m - 3 ∧ i ≥ k then v - 1
  else if j = m - 1 + k ∧ i ≥ k ∧ i < 2 * k then v - 1
  else if j = m - 1 + k ∧ i ≥ 2 * k ∧ n = 12 then v - 4
  else if j = m - 1 + k ∧ i ≥ 2 * k ∧ n ≠ 12 then v - 5
  else if m + k ≤ j ∧ j ≤ n - 2 ∧ i ≥ k then v - 2
  else v

lemma f4_sum_0_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f4_sum n i j < n ∧
    ((j = 0 ∧ (f4_sum n i j = i + n - 2 ∨ f4_sum n i j + 2 = i)) ∨
     (1 ≤ j ∧ j < n / 2 - 2 ∧ (f4_sum n i j = i + 2 * j + 2 ∨ f4_sum n i j + n = i + 2 * j + 2)) ∨
     (j = n / 2 - 2 ∧ f4_sum n i j = i)) := by
  have hp := p4_nat_lt n j hj
  have hv := val_nat_prop n (p4_nat n) i j
  have hf : f4_sum n i j = val_nat n (p4_nat n) i j := by
    dsimp only [f4_sum]; split_ifs <;> omega
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine ⟨by omega, Or.inl ⟨h1, by omega⟩⟩
  · refine ⟨by omega, Or.inr (Or.inl ⟨h1, h2, by omega⟩)⟩
  · refine ⟨by omega, Or.inr (Or.inr ⟨h1, by omega⟩)⟩

lemma f4_sum_1_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n - 5) :
    f4_sum n i j < n ∧
    ((j = n / 2 - 1 ∧ i < n - 1 ∧ f4_sum n i j = i) ∨
     (j = n / 2 - 1 ∧ i = n - 1 ∧ f4_sum n i j = 0) ∨
     (n / 2 ≤ j ∧ j < n - 5 ∧
      (f4_sum n i j + n = i + 2 * j + 3 ∨ f4_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hp := p4_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_prop n (p4_nat n) i j
  dsimp only [f4_sum]
  split_ifs with hs1 hs2 hs3
  · refine ⟨by omega, Or.inl ⟨hs1.1, hs1.2, by omega⟩⟩
  · omega
  · omega
  · by_cases hjm : j = n / 2 - 1
    · refine ⟨by omega, Or.inr (Or.inl ⟨hjm, by omega, by omega⟩)⟩
    · refine ⟨by omega, Or.inr (Or.inr ⟨by omega, hj2, by omega⟩)⟩

lemma f4_sum_2_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
    (hj2 : ¬ j < n - 5) :
    f4_sum n i j < n ∧
    ((j = n - 5 ∧ i < 5 ∧ f4_sum n i j = i + n / 2 - 5) ∨
     (j = n - 1 ∧ i < 2 ∧ f4_sum n i j = i + 1) ∨
     (j = n - 1 ∧ i ≥ 2 ∧ (f4_sum n i j = i + 2 ∨ f4_sum n i j + n = i + 2)) ∨
     (j < n - 1 ∧ (j ≠ n - 5 ∨ i ≥ 5) ∧
      (f4_sum n i j + n = i + 2 * j + 3 ∨ f4_sum n i j + 2 * n = i + 2 * j + 3))) := by
  have hp := p4_nat_ge n j hge (by omega) hjlt
  have hv := val_nat_prop n (p4_nat n) i j
  by_cases hjn1 : j = n - 1
  · have hp1 : p4_nat n j = 2 := by rcases hp with ⟨_, hlt, _⟩ | ⟨_, hp1⟩ <;> omega
    by_cases hi2 : i < 2
    · have hf : f4_sum n i j = val_nat n (p4_nat n) i j - 1 := by
        dsimp only [f4_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inl ⟨hjn1, hi2, by omega⟩)⟩
    · have hf : f4_sum n i j = val_nat n (p4_nat n) i j := by
        dsimp only [f4_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hjn1, by omega, by omega⟩))⟩
  · have hp1 : p4_nat n j = 2 * (j - (n / 2 - 1)) + 1 := by
      rcases hp with ⟨_, _, hp1⟩ | ⟨hjn, _⟩ <;> omega
    by_cases hj5 : j = n - 5 ∧ i < 5
    · have hf : f4_sum n i j = val_nat n (p4_nat n) i j - (n / 2 - 2) := by
        dsimp only [f4_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inl ⟨hj5.1, hj5.2, by omega⟩⟩
    · have hf : f4_sum n i j = val_nat n (p4_nat n) i j := by
        dsimp only [f4_sum]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega⟩))⟩

lemma f4_diff_0_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hj : j < n / 2 - 1) :
    f4_diff n i j < n ∧
    ((j = 0 ∧ (f4_diff n i j = i + n - 2 ∨ f4_diff n i j + 2 = i)) ∨
     (j = n / 2 - 2 ∧ f4_diff n i j = i) ∨
     (1 + n / 3 ≤ j ∧ j ≤ n / 2 - 3 ∧ i ≥ n / 3 ∧ f4_diff n i j + n = i + 2 * j + 1) ∨
     (1 ≤ j ∧ j ≤ n / 2 - 3 ∧ (j < 1 + n / 3 ∨ i < n / 3) ∧
      (f4_diff n i j = i + 2 * j + 2 ∨ f4_diff n i j + n = i + 2 * j + 2))) := by
  have hp := p4_nat_lt n j hj
  have hv := val_nat_prop n (p4_nat n) i j
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
      dsimp only [f4_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inl ⟨h1, by omega⟩⟩
  · by_cases hw : 1 + n / 3 ≤ j ∧ i ≥ n / 3
    · have hf : f4_diff n i j = val_nat n (p4_nat n) i j - 1 := by
        dsimp only [f4_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hw.1, by omega, hw.2, by omega⟩))⟩
    · have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
        dsimp only [f4_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr ⟨h1, by omega, by omega, by omega⟩))⟩
  · have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
      dsimp only [f4_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inr (Or.inl ⟨h1, by omega⟩)⟩

lemma f4_diff_1_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n)
    (hj1 : ¬ j < n / 2 - 1) (hj2 : j < n / 2 - 1 + n / 3) :
    f4_diff n i j < n ∧
    (f4_diff n i j + n = i + 2 * j + 3 ∨ f4_diff n i j + 2 * n = i + 2 * j + 3) := by
  have hp := p4_nat_ge n j hge hj1 (by omega)
  have hv := val_nat_prop n (p4_nat n) i j
  have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
    dsimp only [f4_diff]; split_ifs <;> omega
  rcases hp with ⟨_, _, hp1⟩ | ⟨hjn, _⟩ <;> omega

lemma f4_diff_2_prop (n i j : ℕ) (hmod : n % 6 = 0) (hge : n ≥ 12) (hi : i < n) (hjlt : j < n)
    (hj2 : ¬ j < n / 2 - 1 + n / 3) :
    f4_diff n i j < n ∧
    ((j = n / 2 - 1 + n / 3 ∧ n / 3 ≤ i ∧ i < 2 * (n / 3) ∧ f4_diff n i j + n / 3 = i) ∨
     (j = n / 2 - 1 + n / 3 ∧ i ≥ 2 * (n / 3) ∧ n = 12 ∧ f4_diff n i j + 7 = i) ∨
     (j = n / 2 - 1 + n / 3 ∧ i ≥ 2 * (n / 3) ∧ n ≥ 18 ∧ f4_diff n i j + n / 3 + 4 = i) ∨
     (n / 2 + n / 3 ≤ j ∧ j ≤ n - 2 ∧ i ≥ n / 3 ∧ f4_diff n i j + 2 * n = i + 2 * j + 1) ∨
     (j ≤ n - 2 ∧ i < n / 3 ∧
      (f4_diff n i j + n = i + 2 * j + 3 ∨ f4_diff n i j + 2 * n = i + 2 * j + 3)) ∨
     (j = n - 1 ∧ (f4_diff n i j = i + 2 ∨ f4_diff n i j + n = i + 2))) := by
  have hp := p4_nat_ge n j hge (by omega) hjlt
  have hv := val_nat_prop n (p4_nat n) i j
  by_cases hjn1 : j = n - 1
  · have hp1 : p4_nat n j = 2 := by rcases hp with ⟨_, hlt, _⟩ | ⟨_, hp1⟩ <;> omega
    have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
      dsimp only [f4_diff]; split_ifs <;> omega
    refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hjn1, by omega⟩))))⟩
  · have hp1 : p4_nat n j = 2 * (j - (n / 2 - 1)) + 1 := by
      rcases hp with ⟨_, _, hp1⟩ | ⟨hjn, _⟩ <;> omega
    by_cases hik : i < n / 3
    · have hf : f4_diff n i j = val_nat n (p4_nat n) i j := by
        dsimp only [f4_diff]; split_ifs <;> omega
      refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hik, by omega⟩))))⟩
    · by_cases hjm : j = n / 2 - 1 + n / 3
      · by_cases hi2k : i < 2 * (n / 3)
        · have hf : f4_diff n i j = val_nat n (p4_nat n) i j - 1 := by
            dsimp only [f4_diff]; split_ifs <;> omega
          refine ⟨by omega, Or.inl ⟨hjm, by omega, hi2k, by omega⟩⟩
        · by_cases hn12 : n = 12
          · have hf : f4_diff n i j = val_nat n (p4_nat n) i j - 4 := by
              dsimp only [f4_diff]; split_ifs <;> omega
            refine ⟨by omega, Or.inr (Or.inl ⟨hjm, by omega, hn12, by omega⟩)⟩
          · have hf : f4_diff n i j = val_nat n (p4_nat n) i j - 5 := by
              dsimp only [f4_diff]; split_ifs <;> omega
            refine ⟨by omega, Or.inr (Or.inr (Or.inl ⟨hjm, by omega, by omega, by omega⟩))⟩
      · have hf : f4_diff n i j = val_nat n (p4_nat n) i j - 2 := by
          dsimp only [f4_diff]; split_ifs <;> omega
        refine ⟨by omega, Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, by omega, by omega⟩)))⟩

lemma solve_family4 (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (hmod : n % 6 = 0) (hge : n ≥ 12) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  apply exists_incremental_of_nat n h hn
    (p4_nat n) (f4_sum n) (f4_diff n)
  · intro j hj
    by_cases h1 : j < n / 2 - 1
    · have := p4_nat_lt n j h1; omega
    · have := p4_nat_ge n j hge h1 hj; omega
  · intro j₁ hj₁ j₂ hj₂ heq
    by_cases h1 : j₁ < n / 2 - 1 <;> by_cases h2 : j₂ < n / 2 - 1
    · have := p4_nat_lt n j₁ h1; have := p4_nat_lt n j₂ h2; omega
    · have := p4_nat_lt n j₁ h1; have := p4_nat_ge n j₂ hge h2 hj₂; omega
    · have := p4_nat_ge n j₁ hge h1 hj₁; have := p4_nat_lt n j₂ h2; omega
    · have := p4_nat_ge n j₁ hge h1 hj₁; have := p4_nat_ge n j₂ hge h2 hj₂; omega
  · intro i _ j _; dsimp only [f4_sum]; split_ifs <;> omega
  · intro i _ j _; dsimp only [f4_diff]; split_ifs <;> omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n - 5
      · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n - 5
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_sum_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n - 5 <;> by_cases h2b : j₂ < n - 5
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_sum_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_sum_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_sum_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    by_cases h1a : j₁ < n / 2 - 1 <;> by_cases h2a : j₂ < n / 2 - 1
    · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
      have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_0_prop n i₁ j₁ hmod hge hi₁ h1a
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_diff_0_prop n i₂ j₂ hmod hge hi₂ h2a; omega
    · by_cases h1b : j₁ < n / 2 - 1 + n / 3 <;> by_cases h2b : j₂ < n / 2 - 1 + n / 3
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_1_prop n i₁ j₁ hmod hge hi₁ h1a h1b
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_diff_1_prop n i₂ j₂ hmod hge hi₂ h2a h2b; omega
      · have := f4_diff_2_prop n i₁ j₁ hmod hge hi₁ hj₁ h1b
        have := f4_diff_2_prop n i₂ j₂ hmod hge hi₂ hj₂ h2b; omega

lemma exists_incremental_of_fin_decide
    (n : ℕ) (h : n ≥ 4) (hn : n ≠ 4 ∧ n ≠ 6)
    (p_nat : ℕ → ℕ)
    (f_sum f_diff : ℕ → ℕ → ℕ)
    (h_all :
      (∀ j : Fin n, p_nat j.val < n) ∧
      (∀ j₁ j₂ : Fin n, p_nat j₁.val = p_nat j₂.val → j₁ = j₂) ∧
      (∀ i j : Fin n, f_sum i.val j.val ≤ val_nat n p_nat i.val j.val) ∧
      (∀ i j : Fin n, f_diff i.val j.val ≤ val_nat n p_nat i.val j.val) ∧
      (∀ i₁ j₁ j₂ : Fin n, j₂.val ≤ i₁.val + j₁.val → i₁.val + j₁.val - j₂.val < n →
        f_sum i₁.val j₁.val = f_sum (i₁.val + j₁.val - j₂.val) j₂.val → j₁ = j₂) ∧
      (∀ i₁ j₁ j₂ : Fin n, j₁.val ≤ i₁.val + j₂.val → i₁.val + j₂.val - j₁.val < n →
        f_diff i₁.val j₁.val = f_diff (i₁.val + j₂.val - j₁.val) j₂.val → j₁ = j₂)) :
    ∃ p : Fin n → Fin n, Bijective p ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  rcases h_all with ⟨h1, h2, h3, h4, h5, h6⟩
  apply exists_incremental_of_nat n h hn p_nat f_sum f_diff
  · intro j hj; exact h1 ⟨j, hj⟩
  · intro j₁ hj₁ j₂ hj₂ heq
    exact congrArg Fin.val (h2 ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ heq)
  · intro i hi j hj; exact h3 ⟨i, hi⟩ ⟨j, hj⟩
  · intro i hi j hj; exact h4 ⟨i, hi⟩ ⟨j, hj⟩
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hs hfeq
    have hi2_eq : i₁ + j₁ - j₂ = i₂ := by omega
    rw [← hi2_eq] at hfeq
    exact congrArg Fin.val (h5 ⟨i₁, hi₁⟩ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (by dsimp only; omega) (by dsimp only; omega) hfeq)
  · intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hd hfeq
    have hi2_eq : i₁ + j₂ - j₁ = i₂ := by omega
    rw [← hi2_eq] at hfeq
    exact congrArg Fin.val (h6 ⟨i₁, hi₁⟩ ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ (by dsimp only; omega) (by dsimp only; omega) hfeq)

def p8_nat : ℕ → ℕ
  | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 6 | 5 => 2 | 6 => 7 | _ => 5

def f8_sum (i j : ℕ) : ℕ :=
  if j = 3 ∧ i < 4 then i + 1
  else if j = 3 ∧ i = 4 then 3
  else val_nat 8 p8_nat i j

def f8_diff (i j : ℕ) : ℕ :=
  if j = 6 ∧ (i = 5 ∨ i = 6) then i - 5
  else if j = 6 ∧ i = 7 then 5
  else val_nat 8 p8_nat i j

lemma solve_8 (h : 8 ≥ 4) (hn : 8 ≠ 4 ∧ 8 ≠ 6) :
    ∃ p : Fin 8 → Fin 8, Bijective p ∧ @IsIncremental 8 (@cyclicSquare 8 p h hn) :=
  exists_incremental_of_fin_decide 8 h hn
    p8_nat f8_sum f8_diff (by decide)

def p9_nat : ℕ → ℕ
  | 0 => 0 | 1 => 6 | 2 => 3 | 3 => 1 | 4 => 8 | 5 => 5 | 6 => 2 | 7 => 4 | _ => 7

def f9_sum (i j : ℕ) : ℕ :=
  if j = 5 ∧ i < 3 then i + 4
  else if j = 5 ∧ i = 3 then 2
  else if j = 6 ∧ i < 2 then i
  else if j = 6 ∧ (i = 2 ∨ i = 3) then 2 * i - 3
  else val_nat 9 p9_nat i j

def f9_diff (i j : ℕ) : ℕ := val_nat 9 p9_nat i j

lemma solve_9 (h : 9 ≥ 4) (hn : 9 ≠ 4 ∧ 9 ≠ 6) :
    ∃ p : Fin 9 → Fin 9, Bijective p ∧ @IsIncremental 9 (@cyclicSquare 9 p h hn) :=
  exists_incremental_of_fin_decide 9 h hn
    p9_nat f9_sum f9_diff (by decide)

def p15_nat : ℕ → ℕ
  | 0 => 0 | 1 => 3 | 2 => 6 | 3 => 9 | 4 => 12
  | 5 => 8 | 6 => 5 | 7 => 2 | 8 => 13 | 9 => 1
  | 10 => 4 | 11 => 7 | 12 => 10 | 13 => 14 | _ => 11

def f15_sum (i j : ℕ) : ℕ := val_nat 15 p15_nat i j

def f15_diff (i j : ℕ) : ℕ :=
  if j = 13 ∧ i = 10 then 5
  else if j = 13 ∧ 11 ≤ i ∧ i ≤ 14 then i - 8
  else if j = 14 ∧ (i = 5 ∨ i = 6) then i - 5
  else if j = 14 ∧ 7 ≤ i ∧ i ≤ 10 then i - 6
  else if j = 14 ∧ (i = 11 ∨ i = 12 ∨ i = 14) then 2
  else if j = 14 ∧ i = 13 then 1
  else val_nat 15 p15_nat i j

lemma solve_15 (h : 15 ≥ 4) (hn : 15 ≠ 4 ∧ 15 ≠ 6) :
    ∃ p : Fin 15 → Fin 15, Bijective p ∧ @IsIncremental 15 (@cyclicSquare 15 p h hn) :=
  exists_incremental_of_fin_decide 15 h hn
    p15_nat f15_sum f15_diff (by decide)

def p21_nat : ℕ → ℕ
  | 0 => 0 | 1 => 18 | 2 => 15 | 3 => 12 | 4 => 9 | 5 => 6 | 6 => 3
  | 7 => 7 | 8 => 4 | 9 => 1 | 10 => 14 | 11 => 17 | 12 => 10 | 13 => 16
  | 14 => 2 | 15 => 5 | 16 => 11 | 17 => 8 | 18 => 20 | 19 => 13 | _ => 19

def f21_sum (i j : ℕ) : ℕ :=
  if j = 7 ∧ i ≤ 12 then i + 6
  else if j = 7 ∧ i = 13 then 13
  else if j = 8 ∧ i ≤ 7 then i + 3
  else if j = 8 ∧ 8 ≤ i ∧ i ≤ 10 then i + 2
  else if j = 8 ∧ (i = 11 ∨ i = 13) then i + 1
  else if j = 8 ∧ i = 12 then 9
  else if j = 9 ∧ i ≤ 7 then i
  else if j = 9 ∧ (i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 12 ∨ i = 13) then i - 2
  else if j = 9 ∧ i = 11 then 7
  else if j = 14 ∧ i ≤ 5 then i + 1
  else if j = 14 ∧ i = 6 then 6
  else if j = 14 ∧ 7 ≤ i ∧ i ≤ 9 then i + 1
  else val_nat 21 p21_nat i j

def f21_diff (i j : ℕ) : ℕ :=
  if j = 18 ∧ 16 ≤ i ∧ i ≤ 20 then i - 13
  else if j = 19 ∧ 14 ≤ i ∧ i ≤ 16 then i - 14
  else if j = 19 ∧ 17 ≤ i ∧ i ≤ 20 then i - 17
  else val_nat 21 p21_nat i j

lemma solve_21 (h : 21 ≥ 4) (hn : 21 ≠ 4 ∧ 21 ≠ 6) :
    ∃ p : Fin 21 → Fin 21, Bijective p ∧ @IsIncremental 21 (@cyclicSquare 21 p h hn) :=
  exists_incremental_of_fin_decide 21 h hn
    p21_nat f21_sum f21_diff (by decide)

theorem Conjecture :
  ∀ (n : ℕ)
    (h : n ≥ 4)
    (hn : n ≠ 4 ∧ n ≠ 6),
  ∃ p : Fin n → Fin n,
        Bijective p
      ∧ @IsIncremental n (@cyclicSquare n p h hn) := by
  intro n h hn
  have hmod :
      (n % 6 = 1 ∨ n % 6 = 5) ∨
      ((n % 6 = 2 ∨ n % 6 = 4) ∧ (n = 8 ∨ n ≥ 10)) ∨
      (n % 6 = 3 ∧ (n = 9 ∨ n = 15 ∨ n = 21 ∨ n ≥ 27)) ∨
      (n % 6 = 0 ∧ n ≥ 12) := by omega
  rcases hmod with h1 | ⟨h2, rfl | hge⟩ | ⟨h3, rfl | rfl | rfl | hge⟩ | ⟨h4, hge⟩
  · exact solve_family1 n h hn h1
  · exact solve_8 h hn
  · exact solve_family2 n h hn h2 hge
  · exact solve_9 h hn
  · exact solve_15 h hn
  · exact solve_21 h hn
  · exact solve_family3 n h hn h3 hge
  · exact solve_family4 n h hn h4 hge

def L4_nat : ℕ → ℕ → ℕ
  | 0, 0 => 2 | 0, 1 => 0 | 0, 2 => 1 | 0, _ => 3
  | 1, 0 => 1 | 1, 1 => 3 | 1, 2 => 2 | 1, _ => 0
  | 2, 0 => 0 | 2, 1 => 2 | 2, 2 => 3 | 2, _ => 1
  | _, 0 => 3 | _, 1 => 1 | _, 2 => 0 | _, _ => 2

def L4 (i j : Fin 4) : Fin 4 :=
  ⟨L4_nat i.val j.val % 4, mod_lt _ (by decide)⟩

def L6_nat : ℕ → ℕ → ℕ
  | 0, 0 => 1 | 0, 1 => 0 | 0, 2 => 2 | 0, 3 => 3 | 0, 4 => 5 | 0, _ => 4
  | 1, 0 => 3 | 1, 1 => 1 | 1, 2 => 4 | 1, 3 => 0 | 1, 4 => 2 | 1, _ => 5
  | 2, 0 => 4 | 2, 1 => 3 | 2, 2 => 5 | 2, 3 => 2 | 2, 4 => 1 | 2, _ => 0
  | 3, 0 => 0 | 3, 1 => 2 | 3, 2 => 1 | 3, 3 => 5 | 3, 4 => 4 | 3, _ => 3
  | 4, 0 => 2 | 4, 1 => 5 | 4, 2 => 0 | 4, 3 => 4 | 4, 4 => 3 | 4, _ => 1
  | _, 0 => 5 | _, 1 => 4 | _, 2 => 3 | _, 3 => 1 | _, 4 => 0 | _, _ => 2

def L6 (i j : Fin 6) : Fin 6 :=
  ⟨L6_nat i.val j.val % 6, mod_lt _ (by decide)⟩

lemma isIncremental_of_fin_decide (n : ℕ) (L : Fin n → Fin n → Fin n)
    (h_decide :
      (∀ i j₁ j₂ : Fin n, L i j₁ = L i j₂ → j₁ = j₂) ∧
      (∀ j i₁ i₂ : Fin n, L i₁ j = L i₂ j → i₁ = i₂) ∧
      (∀ k : Fin n, ∀ s : Fin (2 * n - 1),
        #(sumDiagOk n s.val k.val L) ≤ k.val + 1) ∧
      (∀ k : Fin n, ∀ d : Fin (2 * n - 1),
        #(diffDiagOk n ((d.val : ℤ) - ((n : ℤ) - 1)) k.val L) ≤ k.val + 1)) :
    IsIncremental n L := by
  rcases h_decide with ⟨hrow, hcol, hsum, hdiff⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hrow i, rfl⟩
  · intro j
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hcol j, rfl⟩
  · intro k hk
    refine ⟨?_, ?_⟩
    · intro s
      by_cases hs : s < 2 * n - 1
      · exact hsum ⟨k, hk⟩ ⟨s, hs⟩
      · have hemp : sumDiagOk n s k L = ∅ := by
          ext ⟨i, j⟩
          simp only [sumDiagOk, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          have := i.isLt; have := j.isLt; omega
        rw [hemp, Finset.card_empty]; omega
    · intro d
      by_cases hd : -(n : ℤ) + 1 ≤ d ∧ d ≤ (n : ℤ) - 1
      · let d_nat : ℕ := (d + ((n : ℤ) - 1)).toNat
        have hd_lt : d_nat < 2 * n - 1 := by omega
        have hd_eq : ((d_nat : ℤ) - ((n : ℤ) - 1)) = d := by omega
        rw [← hd_eq]
        exact hdiff ⟨k, hk⟩ ⟨d_nat, hd_lt⟩
      · have hemp : diffDiagOk n d k L = ∅ := by
          ext ⟨i, j⟩
          simp only [diffDiagOk, Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.notMem_empty, iff_false]
          have := i.isLt; have := j.isLt; omega
        rw [hemp, Finset.card_empty]; omega

lemma isIncremental_L4 : IsIncremental 4 L4 :=
  isIncremental_of_fin_decide 4 L4 (by decide)

lemma isIncremental_L6 : IsIncremental 6 L6 :=
  isIncremental_of_fin_decide 6 L6 (by decide)

end IncrementalCyclic
