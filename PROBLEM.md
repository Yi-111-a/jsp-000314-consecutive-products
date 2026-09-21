# JSP-000314 — How many starting points make the largest prime factor repeat in a product of consecutive integers, and what is their density?

- **id:** JSP-000314
- **title:** How many starting points make the largest prime factor repeat in a product of consecutive integers, and what is their density?
- **area:** Number theory
- **status:** Solved
- **Lean:** No (formalization target)
- **Eligible / Claim:** No / Unavailable
- **role:** Formalize path (Solved + Lean=No)

## Statement

How many starting points make the largest prime factor repeat in a product of consecutive integers, and what is their density?

## Catalog

- Anchor: https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000314
- Awards home: https://github.com/TheJustinSunPrize/awards

## Primary papers

- Tao (Ta26c), arXiv:2603.27990 (2026) — full resolution

## Accepted mathematical answer

Tao (Ta26c, arXiv:2603.27990) proved the Erdős–Graham conjecture: with B(x) the number of n≤x contained in at least one bad interval of consecutive integers (product divisible by the square of its largest prime factor), B(x) = (1 + O((log x)^{-1+o(1)})) · #{n≤x : P(n)^2 | n}. A mere density-zero or x^{1−o(1)} lower bound is not the full answer.

## Success criteria

- `lake build` succeeds
- Zero `sorry` / `admit`
- Named headline theorem(s) in ACCEPTANCE.md proved
