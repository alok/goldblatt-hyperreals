# Lectures on the Hyperreals, in Lean 4

A chapter-by-chapter Lean 4 / Mathlib formalization of Robert Goldblatt's
*Lectures on the Hyperreals: An Introduction to Nonstandard Analysis*
(Springer GTM 188), published as a literate [Verso](https://github.com/leanprover/verso) site:

**<https://alok.github.io/goldblatt-hyperreals/>**

Each chapter of the book is one Lean module and one page of the site.
See [SPEC.md](SPEC.md) for the design and [COVERAGE.md](COVERAGE.md) for the
status of every numbered theorem and exercise.

```bash
lake exe cache get          # Mathlib build cache
lake build                  # check everything
lake query :literateHtml    # build the site, prints its path
```

The prose here is original exposition; the book itself is not reproduced.
