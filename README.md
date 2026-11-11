# Incremental (n, c)-Coins Formalization

Formal verification in Lean 4 of incremental $n \times n$ Latin squares and cyclic incremental $n \times n$ Latin squares representing $n + 1$ solutions of $(n, c)$-coins problems simultaneously for all $0 \le c \le n$.

## Main Results

- **`IncrementalCyclic.incremental_represents_nc_coins`**: For every $n \ge 4$ and $0 \le c \le n$, every incremental $n \times n$ Latin square $L$ represents a valid $(n, c)$-coins solution `coinsFromSquare n c L`.
- **`IncrementalCyclic.exists_cyclic_incremental`**: For every $n \ge 4$ with $n \notin \{4, 6\}$, there exists a bijection $p : \mathrm{Fin}\, n \to \mathrm{Fin}\, n$ such that the cyclic Latin square $L(i, j) = (i + p(j)) \bmod n$ is incremental.
- **`IncrementalCyclic.exists_incremental_ge_4`**: For every $n \ge 4$, there exists an incremental $n \times n$ Latin square $L$ (cyclic for $n \notin \{4, 6\}$, and explicit non-cyclic squares `L4` and `L6` for $n \in \{4, 6\}$).
- **`IncrementalCyclic.exists_incremental_representing_nc_coins`**: Combined theorem establishing that for every $n \ge 4$, there exists an incremental $n \times n$ Latin square simultaneously representing $(n, c)$-coins solutions for all $0 \le c \le n$.

## Repository Structure

- `Challenge.lean` — The main theorems.
- `Solution.lean` — Proves the main theorems declared in `Challenge.lean`.

and

- `IncrementalNCCoins/Basic.lean` — Basic definitions
- `IncrementalNCCoins.lean` — Supporting lemmas and constructions (the injective-majorization principle, the four modular families modulo 6, and the exceptional cases $n \in \{4, 6, 8, 9, 15, 21\}$).

and

- `comparator.json` — Configuration for `lake comparator`.
- `formalization.yaml` — Palomar Registry metadata.

## Verification & Submission

```bash
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

Submit to the Palomar Registry at https://submit.palomar-registry.org/ using the full 40-character commit SHA.
