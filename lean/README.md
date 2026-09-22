# JSP-000314 Lean project

Formalization of the Erdős–Graham conjecture as resolved by Tao (Ta26c,
arXiv:2603.27990): the count `B(x)` of `n ≤ x` lying in a bad interval
(product of consecutive integers divisible by the square of its largest
prime factor) satisfies
`B(x) = (1 + O((log x)^{-1+o(1)})) · #{n ≤ x : P(n)^2 | n}`.

## Build

Requires elan with the toolchain pinned in `lean-toolchain`
(`leanprover/lean4:v4.34.0`) and Mathlib `v4.34.0`.

```sh
export PATH="$HOME/.elan/bin:$PATH"
cd problems/JSP-000314/lean
lake build
```

## Layout

- `JSP314/Defs.lean` — `largestPrimeFactor`, `IsBadInterval`, `B`,
  `badSingletonCount` and the `largestPrimeFactor` API.
- `JSP314/Bounds.lean` — elementary comparisons `S(x) ≤ B(x) ≤ x+1`.
- `JSP314/ProdLPF.lean` — `P(∏_{i=u}^{v} i) = max_{i ∈ [u,v]} P(i)`.
- `JSP314/Localization.lean` — a `P²`-multiple inside a bad interval is a
  bad singleton; every interval point is within `v - u` of it.
- `JSP314/Counting.lean` — `π(√x) ≤ S(x)` via prime squares.
- `JSP314/Main.lean` — headline `bad_interval_count_asymptotic`, proved
  modulo the single analytic core lemma `badNonSingleton_interval_bound`
  (the deep content of Ta26c).

## Headline theorem

`JSP314.bad_interval_count_asymptotic`
