# ACCEPTANCE — JSP-000314 (prize-ready gate)

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000314
- Awards CONTRIBUTING: https://github.com/TheJustinSunPrize/awards/blob/main/CONTRIBUTING.md

## Exact original question (English)

> How many starting points make the largest prime factor repeat in a product of consecutive integers, and what is their density?

The accepted resolution: Tao (Ta26c, arXiv:2603.27990) proved the Erdős–Graham conjecture: with B(x) the number of n≤x contained in at least one bad interval of consecutive integers (product divisible by the square of its largest prime factor), B(x) = (1 + O((log x)^{-1+o(1)})) · #{n≤x : P(n)^2 | n}. A mere density-zero or x^{1−o(1)} lower bound is not the full answer.

## Required Lean theorem name(s) (FULL statement)

| Lean name | Intended statement |
|---|---|
| `bad_interval_count_asymptotic` | Ta26c: if B(x) counts n≤x lying in some bad interval (product of consecutives divisible by square of its largest prime factor), then B(x) = (1 + O((log x)^{-1+o(1)})) · #{n≤x : P(n)^2 | n}. |

**Not sufficient for prize_ready:** weaker special cases, finite truncations, or intermediate lemmas alone.

## Checklist (all must pass)

- [ ] `lake build` succeeds in `lean/`
- [ ] Zero `sorry` / `admit` in all `*.lean` (excluding `.lake`)
- [ ] `#print axioms` on headline theorem(s) shows only standard axioms
- [ ] Public repo HEAD is a full 40-character commit SHA
- [ ] README documents build instructions
- [ ] `formalization.yaml` and/or `ATTRIBUTION.md` name `Yi-111-a` / operators
- [ ] Named headline theorem(s) above exist and are proved

## Harness rule

`prize_ready=true` **only** when every checklist item passes **and** the named headline theorem(s) exist and are proved.
