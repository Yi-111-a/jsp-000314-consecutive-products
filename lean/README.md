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
- `JSP314/Squeeze.lean` — every non-singleton bad interval satisfies
  `v + 2 ≤ 2u` (Bertrand's postulate: a prime in `(v/2, v]` lies in the
  interval and occurs to the first power only).
- `JSP314/Type2Run.lean` — type-2 dichotomy branch: if no element of a bad
  `[u,v]` is divisible by `P²`, then `P` divides two distinct elements,
  hence `P ≤ v - u`; every element is `P`-smooth.
- `JSP314/Main.lean` — headline `bad_interval_count_asymptotic`, proved
  modulo the single analytic core lemma `badNonSingleton_interval_bound`
  (the deep content of Ta26c).

The `attempts/` tree holds auxiliary development files (not part of the
default target): `aux/ProdLPF.lean` (`P(∏_{i=u}^{v} i) = max_i P(i)`),
`aux/Localization.lean` (a `P²`-multiple in a bad interval is a bad
singleton), `aux/Counting.lean` (`π(√x) ≤ S(x)`), `aux/SylvesterSchur.lean`,
`aux/TypeIBound.lean`, `aux/TypeIIEmpty.lean`, and related scratch work.

## Headline theorem

`JSP314.bad_interval_count_asymptotic`
