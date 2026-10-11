# Repository instructions

<INSTRUCTIONS>
Avoid the prohibited vocabulary specified by the active session instructions. Do not use bold
characters. In mathematical proofs, do not label arguments as numbered steps. Write mathematical
formulas with `$ $`; HTML mathematics must use MathJax.

Shortcut tags at the start of a query have the following meanings.

- `[math]`: act as a research-level mathematics professor and favor formulas in proof arguments.
- `[PHYS]`: act as a professional physicist.
- `[proofcheck]`: check the proof line by line and report only errors that have been verified.
- `[numcheck]`: test the claim or conjecture numerically.
- `[TEACH]`: explain at bachelor mathematical-physics level in a kind and warm style.
- `[REPHRASE]`: rewrite the input as a precise, self-contained research-level problem statement;
  list assumptions, define symbols, and add only minimal standard assumptions.

The goal is to fill in the `sorry`s in `SpinGlass/Parisi/ParisiLowerBound.lean` without changing any claims therein.

Current Chapter 14 status: `SpinGlass/Parisi/ParisiFullMin.lean` proves
`exists_randomFieldParisiMIN`, providing strict mass and overlap parameters,
near-infimum value, overlap minimization, and full fixed-level minimization on
the closed parameter domain. `SpinGlass/Parisi/ParisiMVariation.lean` defines an
overlap/mass insertion and proves left-endpoint, right-endpoint, and matching-mass
functional identities. The mass derivative estimates, coupled main estimate,
concentration, localization, interpolation lower comparison, and the nondegenerate
theorem in `ParisiLowerBound.lean` remain open. Build these leaf modules explicitly;
`SpinGlass.lean` does not yet import the lower-bound capstone.

## Parisi overlap-derivative completion criteria

When working on `SpinGlass/Parisi/ParisiQDeriv.lean`, the claims attributed to Talagrand,
Vol. II, Section 14.7 are complete only when the following conditions hold.

- Define the concrete moment
  `$M_r = \mathbb E(W_1\cdots W_{r-1}A'_r(\zeta_r)^2)$` from the actual Parisi recursion.
- Specialize the generic Cole-Hopf split and propagation theorems to `parisiX₀`; do not leave
  its derivative as a hypothesis in the final book-level theorem.
- Treat `$q_1=0$` and `$q_{k+1}=1$` by admissible one-sided variations or a proved nearby-sign
  argument. Do not assume a two-sided derivative across a clamped zero variance.
- Derive positivity of the first moment from a probability law for the i.i.d. external field and
  its nondegeneracy assumption, corresponding to `$\mathbb E h^2>0$` in the book.
- Derive strict boundedness of the last moment from `$|\tanh x|<1$` and the Cole-Hopf recursion.
- Derive the required properties of `$ξ$` from a named version of (14.101), including the
  treatment of `$ξ''(0)=0$`; do not assume positivity at zero merely to rule out `$q_1=0$`.
- For the random-field theorem, instantiate differentiation under the external-field integral
  and require that the site law is a probability measure. The final moment must be explicitly
  identified with the corresponding i.i.d. product-coordinate expectation.
- The final theorem corresponding to Proposition 14.7.5 must follow from the book-level
  assumptions, admissibility, and minimization, without hypotheses that restate (14.219), endpoint
  moment bounds, or (14.222).
- Preserve useful abstract intermediate lemmas, but label conditional reductions accurately.
- Verify with `lake build SpinGlass.Parisi.ParisiQDeriv`, run `git diff --check`, and leave no
  `sorry` or `admit` in the completed development.
</INSTRUCTIONS>
