# Erdős Problem 107: the Erdős–Szekeres bounds

A Lean 4 proof of `Erdos107.ersz_bounds` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
Let `f n` be the least `N` such that any `N` points in the plane, no three on a line, contain
the vertices of a convex `n`-gon. Erdős and Szekeres proved, for every `n ≥ 3`,

```text
2^(n-2) + 1 ≤ f n ≤ C(2n-4, n-2) + 1.
```

The upper bound (1935) and the existence of `f n` are taken from Linmiao Xu's formalization
[linrock/math-proofs, erdos-107](https://github.com/linrock/math-proofs/tree/994b4c04dc4cf77c4b27364e27f179622104c681/erdos-107)
(Apache-2.0). This repository adds the lower bound (1960/61) for all `n`, which that
formalization proves only for `n ≤ 5`. See [Erdős Problem 107](https://www.erdosproblems.com/107).

## Files

- `Challenge.lean`: the statement. It imports only Mathlib. `cardSet`, `f` and `ersz_bounds` are
  copied from `FormalConjectures/ErdosProblems/107.lean` at commit
  `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`, in the namespace `Erdos107.Palomar`.
- `Proofs/ErdosSzekeresLower107.lean`: the lower bound construction (new).
- `Proofs/Erdos107Unified435.lean`, `Proofs/InductiveKCupKCapConvexityAndKKSWedgePentagonForcing107.lean`,
  `Proofs/XMonotonePerturbationBridgeAndWedgePigeonholePentagon107.lean`, `Proofs/Blueprint107.lean`:
  Linmiao Xu's files, unchanged (see `THIRD_PARTY.md`).
- `Solution.lean`: the proved statement, checked against `Challenge.lean` by `lake comparator`.

## The lower bound

- A *cup* is a set of points whose triples, read from left to right, all turn left; a *cap* is a
  set whose triples all turn right.
- Moving a finite set `B` by `(s, s²)` for large `s` puts it to the right of a finite set `A`.
  Every chord from `A` to the moved `B` is then steeper than every chord inside it, and turns left
  after every chord inside `A`. In the union, a cup that meets `A` keeps at most one point
  outside `A`, and a cap that meets the moved `B` keeps at most one point of `A`.
- Gluing a block with short cups to a block with short caps this way gives, for all `a b`, a set
  of `C(a+b, a)` points with no cup of more than `a + 1` points and no cap of more than `b + 1`
  points.
- The points of a convex polygon split into a cup and a cap that share the leftmost and the
  rightmost point. A point that breaks this would lie in the convex hull of the others.
- Gluing the blocks of sizes `C(n-2, 0), …, C(n-2, n-2)` one after another gives `2^(n-2)`
  points, no three on a line, with no convex `n`-gon: a convex polygon that meets the last block
  and an earlier one has a cup of at most `j + 2` points and a cap of at most `n - j - 1` points.

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux with bubblewrap
```

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions go through the [Palomar submission form](https://submit.palomar-registry.org/).
