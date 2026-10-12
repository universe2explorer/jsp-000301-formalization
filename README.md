# JSP-000301 — Lean formalization of Golomb's counterexample

Formalizes the scoped JSP-000301 question (first yes/no subquestion of
Erdős Problem 365): *If two consecutive positive integers are powerful,
must at least one be a perfect square?* Answer: **No** — Golomb (1970):
12167 = 23^3 and 12168 = 2^3 * 3^2 * 13^2.

Main theorems (in `Jsp000301/Basic.lean`):
- `golomb_counterexample` — existential form of the counterexample
- `answer_no` — negation of the universal assertion
- `powerful_iff_factorization` — the `Powerful` predicate agrees with
  the factorization formulation (every prime divisor occurs with
  exponent at least 2)

## Reproduce
Toolchain: Lean `v4.22.0` (see `lean-toolchain`), Mathlib `v4.22.0`.

```bash
lake exe cache get
lake build
```

Expected: `Build completed successfully`, and the root module prints
that `golomb_counterexample` and `answer_no` depend only on the
standard axioms `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no custom axioms, no `native_decide`.

Mathematical source: S. W. Golomb, "Powerful numbers",
Amer. Math. Monthly 77(8) (1970), 848–852, DOI 10.2307/2317020.
Scope note: this covers only the yes/no subquestion recorded in
JSP-000301 (official review note, 2026-09-13), not the separate
counting question in the full Erdős Problem 365.
