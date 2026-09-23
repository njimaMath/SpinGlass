# EDITING_PLAN.md

## Goal and success condition

Finish Talagrand's Chapter 14 proof of the Parisi lower bound in `njimaMath/SpinGlass`, culminating in a proof of

```lean
eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
```

in `SpinGlass/Parisi/ParisiLowerBound.lean`, without strengthening its assumptions.

This plan is intentionally written as an execution plan for a single long coding pass. The order below is topological: later phases should not be started by inserting placeholders for earlier phases.

## Phase 0 — Baseline and guardrails

### Read first

Read, in this order:

- `AGENTS.md`
- `ARCHITECTURE.md`
- `SpinGlass/Parisi/ParisiLowerBound.lean`
- `SpinGlass/Parisi/ParisiMin.lean`
- `SpinGlass/Parisi/ParisiQDeriv.lean`
- `SpinGlass/Parisi/CoupledProp.lean`
- `SpinGlass/Parisi/CoupledLambdaZero.lean`
- `SpinGlass/Parisi/CoupledDeriv.lean`
- `SpinGlass/Parisi/CoupledSecondDeriv.lean`
- Talagrand Vol. II §§14.5–14.10.

### Establish the real compile baseline

Run:

```bash
lake env lean SpinGlass/Parisi/ParisiLowerBound.lean
```

Record the exact proof hole/error state. Do not infer the state from `lake build` because the umbrella import does not currently force this leaf into the default build.

### Search before adding

Before defining any new object, search for its conceptual equivalent in:

```text
SpinGlass/Parisi/
SpinGlass/FiniteGibbs/
Common/Mathlib/Probability/PointProcess/
Common/Mathlib/Probability/Distributions/Gaussian*
```

The repo already contains most cascade, coupled interpolation, Gaussian concentration, and derivative machinery.

---

## Phase 1 — MIN parameters: full Lemma 14.5.5

### Objective

Upgrade the current “near-infimum admissible parameters exist” result in `ParisiMin.lean` to the full content of Talagrand's Definition 14.5.3 + Lemma 14.5.5: near-global-optimality **and** exact finite-dimensional minimality, followed by deletion of redundant levels to obtain strict admissibility.

Talagrand's MIN conditions are:

```text
0 < m₁ < ... < m_k < 1,
0 ≤ q₁ < q₂ < ... < q_k < q_{k+1} ≤ 1,
P_k(m,q) ≤ P + ε,
P_k(m,q) is minimal among the closed k-level parameter domain.
```

### 1A. Closed parameter domains

Introduce/identify compact domains for fixed `k`.

Suggested shape:

```lean
def ParisiMClosed {k : ℕ} (ms : Fin k → ℝ) : Prop :=
  Monotone ms ∧ (∀ i, 0 ≤ ms i) ∧ ∀ i, ms i ≤ 1

def ParisiQClosed {k : ℕ} (qs : Fin (k + 1) → ℝ) : Prop :=
  Monotone qs ∧ 0 ≤ qs 0 ∧ qs (Fin.last k) ≤ 1
```

Do not duplicate an existing equivalent definition if one already exists.

Prove the fixed-dimensional set is compact. The easiest Lean route should use finite products / `Set.Icc` and closedness of monotonicity inequalities.

### 1B. Joint continuity on the closed domain

Current code documents continuity in the exponents and fixed-q continuity, but MIN needs enough **joint** continuity to attain a minimum over all `m,q` for fixed `k`.

Prove a theorem of the form:

```lean
ContinuousOn
  (fun p : (Fin k → ℝ) × (Fin (k+1) → ℝ) =>
     randomFieldParisiFunctional μh ξ p.1 p.2)
  closedParisiParameterSet
```

or an equivalent sequential/compact formulation.

Be careful at mass `m = 0`: the recursion must use the repository's already established continuous extension, not division by zero.

### 1C. Attainment of fixed-k minimum

From compactness + continuity, prove existence of `(ms*, qs*)` minimizing the functional over the closed domain.

Then combine with `exists_randomFieldParisiFunctional_lt_inf_add_of_talagrand`:

- first choose some strict admissible k-level parameters with value `< inf + ε`;
- minimize over the **same fixed `k`** closed domain;
- the minimum is no larger than the chosen value, hence still `< inf + ε`.

This exactly matches the book's proof strategy.

### 1D. Deletion / normalization lemmas

Formalize the semantic invariances used to remove redundant parameters.

Needed cases:

- if a mass equals `1` at the end, delete the redundant last mass/overlap level;
- if first mass equals `0`, delete first mass and matching q-level;
- if two consecutive masses are equal, merge/delete the redundant level;
- if two consecutive q-values are equal, delete one q and matching mass;
- preserve the value of `randomFieldParisiFunctional` under each deletion.

Use explicit `Fin` reindexing helpers and prove equality of the recursion/functionals. Avoid giant `simp` proofs that obscure which coordinate is deleted.

### 1E. Package MIN

Define a reusable proposition, unless an equivalent already exists, e.g.

```lean
structure RandomFieldParisiMIN
    (μh : Measure ℝ) (ξ : ℝ → ℝ) {ε : ℝ} where
  k : ℕ
  ms : Fin k → ℝ
  qs : Fin (k + 1) → ℝ
  hm : ParisiMAdmissible ms
  hq : ParisiQAdmissible qs
  nearInf : randomFieldParisiFunctional μh ξ ms qs ≤ randomFieldParisiInf μh ξ + ε
  qMin : IsRandomFieldParisiQMinimizer μh ξ ms qs
  fullMin : ... -- no admissible closed-domain (m,q) lowers the value
```

If a structure creates too much refactoring, use a theorem returning a tuple of named hypotheses. The important part is to avoid passing 15 unrelated hypotheses by hand through every main-estimate lemma.

### Exit criterion

Have a theorem corresponding to Lemma 14.5.5 that directly supplies strict `m`, strict `q`, near-infimum value, and finite-dimensional minimality.

Compile `ParisiMin.lean` before proceeding.

---

## Phase 2 — §14.7 variational package beyond q-stationarity

### Objective

The q-derivative layer is already substantially formalized in `ParisiQDeriv.lean`, including the concrete random-field version of Proposition 14.7.5. The missing work is the **mass/splitting variation package** that produces Talagrand's `Φ(m,u)`, `U(v)`, `f(u)` and the quantitative estimates needed by §§14.8–14.10.

Create `SpinGlass/Parisi/ParisiMVariation.lean` unless these lemmas fit naturally at the end of `ParisiQDeriv.lean`.

### 2A. Split one q interval

For fixed `r`, define the operation that inserts a new overlap `u` into `[q_{r-1},q_r]` (and the mirror insertion into `[q_r,q_{r+1}]`) together with a free inserted mass `m`.

The definition should be a reusable reindexing operation on `Fin`, not a one-off list manipulation inside a proof.

Prove endpoint simplifications:

- at `u = q_r`, the inserted interval disappears;
- for `r ≥ 2`, at `u = q_{r-1}`, the other inserted interval disappears;
- at matching masses, the split functional reduces to the original functional.

These identities are used repeatedly in Talagrand's (14.251).

### 2B. Define Φ, U, f in Lean-native terms

Mirror the book but express them through the existing recursion/Cole–Hopf API.

The exact names may differ, but document the correspondence:

```text
Talagrand Φ(m,u)   = split Parisi functional
Talagrand U(v)     = mass derivative of the appropriate split recursion
Talagrand f(u)     = ∂Φ/∂m at m = m_{r-1}
```

Prove the identity corresponding to (14.239):

```text
f(u) = 1/2 * U(ξ'(q_r)-ξ'(u)) - 1/2 * (θ(q_r)-θ(u)).
```

### 2C. U calculus

Using existing Cole–Hopf derivative infrastructure, prove the analogues of Lemma 14.7.4 / Propositions 14.7.7–14.7.8:

- formulas for `U'`, `U''`;
- `U''(v) < 0` on the required variance interval;
- `U'(0) = q_r` by the existing Proposition 14.7.5 stationarity identity.

Keep every integration-under-parameter hypothesis explicit. Reuse the repository's bounded derivative results rather than reproving domination from scratch.

### 2D. f identities and uniform bounds

Prove:

- `f(q_r)=0`;
- `f'(q_r)=0`;
- `r ≥ 2 → f(q_{r-1})=0`;
- `|∂Φ/∂m| ≤ M` or a Lean-friendly uniform-bound theorem sufficient for the next steps;
- `|f'''(u)| ≤ M` on the physical interval.

`f(q_{r-1})=0` needs **full MIN minimality in the mass coordinate**, not merely q-minimality. This is why Phase 1 must come first.

### 2E. Approximate minimality estimate

Formalize Talagrand's “if the chosen MIN value is within ε of the global infimum then no split can improve it by more than ε” argument to get the analogue of:

```text
f(u) ≥ -M * sqrt ε
```

uniformly in the relevant u range.

This estimate is one of the key quantitative bridges from `MIN(ε)` to the main estimate.

### 2F. Nondegenerate-field lower bound on q₁

Prove the analogue of Lemma 14.7.15:

```text
q₁ ≥ 1 / M
```

with `M` depending only on the profile and the nondegenerate external-field law, not on k or the particular MIN approximation once ε is sufficiently small.

Use the random-field expectation already present in `randomFieldParisiQMoment`; do not reduce to a deterministic field.

### 2G. Curvature estimate (14.283)

Prove the quantitative estimate equivalent to:

```text
-f''(q_r)
 = 1/2 * ξ''(q_r) * (-ξ''(q_r) U''(0) - 1)
 ≤ M * ε^(1/6).
```

Talagrand's proof splits depending on whether `q_r - ε^(1/6) ≥ q_{r-1}` and uses either `f ≥ -M√ε` or the endpoint identity `f(q_{r-1})=0` plus the third-derivative bound. Preserve that case split; it gives the scale needed in the critical cases.

### Exit criterion

A main-estimate file should be able to import one module and obtain all §14.7 facts without reopening the Cole–Hopf recursion proof.

---

## Phase 3 — Coupled-copy adapters for a shared i.i.d. field

### Objective

Make the existing §14.6 coupled bound easy to consume by the main estimate in the **random-field** setting.

### 3A. Shared-field law adapter

Prove a clean theorem that specializes the coupled bound to

```lean
a = sharedReplicaSiteField hVec
```

then integrates `hVec` against `externalFieldVecLaw N μh`.

The resulting theorem should expose exactly the random-field analogue of the bound on `Ψ_r(t,u)`.

### 3B. Canonical parameter witness constructors

The seven cases in §§14.8–14.10 repeatedly choose a nondecreasing extended sequence `(ρ_p,n_p)`, a splitting level `τ`, a sign `η`, and sometimes a λ.

Create helper constructors that return both the sequence and proofs of its monotonicity/range conditions. Suggested families:

- `leftNearMainParams`
- `leftFarMainParams`
- `rightNearMainParams`
- `rightFarMainParams`
- `outsideIntervalMainParams`

Names are flexible. The key is to isolate `Fin`/index bookkeeping from the analytic proof.

### 3C. λ=0 and Taylor in the random-field theorem shape

Wrap existing results so that case proofs can invoke:

```text
RHS(0) = 2 * randomFieldParisiFunctional ...
RHS(λ) ≤ RHS(0) + λ * slopeAtZero + λ²/2
```

without manually reconstructing `pairSiteY₀` arguments.

### Exit criterion

A case proof should be able to say “apply coupled bound with this witness; rewrite λ=0; apply Taylor; now prove a scalar inequality” without touching tree/cascade internals.

---

## Phase 4 — Theorem 14.5.7: uniform main estimate

Create `SpinGlass/Parisi/ParisiMainEstimate.lean`.

### Target theorem shape

Aim for a theorem structurally equivalent to:

```lean
∃ K > 0, ∀ N t r u,
  t ∈ Icc 0 t₀ →
  realizableOverlap N u →
  coupledPressure ... r t u
    ≤ 2 * parisiSide t - (u - q_r)^2 / K
```

The exact repository objects may differ, but preserve these uniformities:

- `K` independent of `N`;
- `K` independent of `t ≤ t₀`;
- `K` independent of `u`;
- after fixed finite k, independent of the selected r, or obtained by a finite max over r.

### 4A. Near-left case — Proposition 14.8.1

Range:

```text
q_{r-1} ≤ u ≤ q_r,
M₁(q_r-u) ≤ 1-t₀.
```

Use the split parameter witness with `m = m_{r-1}`, Taylor in λ, and the critical derivative estimate from Phase 2. Optimize λ explicitly to get a quadratic gain.

### 4B. Far-left case — Proposition 14.8.2

For `r ≥ 2` and

```text
q_{r-1} ≤ u ≤ q_r,
M₁(q_r-u) ≥ 1-t₀,
```

prove a **strict** improvement first. Talagrand uses the `f(u) ≥ -M√ε` estimate and strict convexity through the function

```text
γ(c) = inf |ξ(y)-ξ(x)+(x-y)ξ'(y)|, |x-y|>c.
```

Formalize a compactness proof that `γ(c)>0` for `c>0` under `TalagrandXiCondition`.

Then turn strict improvement on the compact “far” set into a uniform gap, using upper semicontinuity/continuity of the explicit witness bound. You do not need to formalize the full abstract `Ψ*` if your explicit bound is continuous and sufficient.

### 4C. r=1 special left/negative case — Proposition 14.8.3

Cover `|u| ≤ q₁`. This is where the nondegenerate-field lower bound on `q₁` matters.

Keep negative overlaps separate from the η=+1 coupling where needed. Reuse the η=-1 side of `CoupledProp` instead of pretending evenness eliminates all sign issues automatically.

### 4D. Near-right case — Proposition 14.8.4

Mirror 4A with the interval `[q_r,q_{r+1}]` and the corresponding inserted mass.

### 4E. Far-right case — Proposition 14.8.5

Mirror 4B. Reuse a common scalar lemma where possible rather than copy/paste the entire analytic argument.

### 4F. Outside-neighbor interval — Proposition 14.8.6

For `t>0` and `u < q_{r-1}` or `u > q_{r+1}`, prove strict improvement using the coarse coupled parameter choice from Talagrand §14.10.

This case should not need the delicate λ Taylor argument.

### 4G. t=0 case — Proposition 14.8.7

Prove strict improvement for `t=0`, `u ≠ q_r`.

Because `t=0` often simplifies the Hamiltonian, isolate this as its own lemma rather than forcing the `t>0` argument through a singular limit.

### 4H. Assemble a single K

The book combines “quadratic near” and “strict far” statements. In Lean, do this explicitly:

- define the compact far region for each r;
- obtain a positive minimum gap there;
- because `(u-q_r)^2 ≤ 4`, convert the gap `δ` to a quadratic form with `K ≥ 4/δ`;
- take a finite maximum over r and over the constants from all cases.

### Exit criterion

Have one theorem corresponding to (14.112), with the same uniformity. Compile this file independently.

---

## Phase 5 — Proposition 14.5.8: exponential constrained-mass estimate

Create `SpinGlass/Parisi/ParisiConcentration.lean`.

### 5A. Define the constrained/unconstrained recursion pair

Use existing cascade recursion notation wherever possible. Introduce Lean objects corresponding to:

```text
J_{k+1}(u), J_{k+1}, ..., J_1(u), J_1,
V_p = exp(m_p^* (J_{p+1}-J_p)),
B = exp(J_{k+1}(u)-J_{k+1}) ≤ 1.
```

### 5B. Recursive inequality (14.120)

Prove the decreasing-induction inequality that compares `J_{p+1}(u)` with `J_{p+1}` and the future weighted product.

This is mostly Jensen/Hölder/cascade recursion algebra; reuse point-process identities already in `Common`.

### 5C. Turn pressure gap into expectation gap

From

```text
E J₁(u) ≤ E J₁ - ε₂ N
```

obtain a negative expectation for the logarithm of the weighted product.

### 5D. Gaussian concentration

Represent the Gaussian Hamiltonian as a linear image of a standard Gaussian vector using existing Gaussian-field infrastructure. Prove the relevant log weighted-product map is `O(√N)`-Lipschitz.

Important random-field rule:

- condition on the site field `hVec`;
- the field enters as an affine shift and does not change the Gaussian Lipschitz constant;
- obtain a concentration bound uniform in the realized `hVec`;
- integrate over `externalFieldVecLaw` only afterwards.

Do **not** assume a concentration inequality for `μh`.

### 5E. Final estimate

Prove the random-field version of Proposition 14.5.8:

```text
strict constrained-pressure gap
→ Gibbs pair mass at exact overlap u and meeting level r ≤ K exp(-N/K).
```

Uniformity: K independent of `u,N,t` once MIN parameters and the strict gap are fixed.

### Exit criterion

One theorem consumable directly by localization.

---

## Phase 6 — Proposition 14.5.6: overlap localization

Create `SpinGlass/Parisi/ParisiLocalization.lean`.

### 6A. Define the bad overlap event

For fixed r, define

```text
A = {(R₁₂-q_r)^2 ≥ K (ψ(t)-φ_N(t)+ε₁)}.
```

### 6B. Use the main estimate

For every realizable `u` in A, combine:

```text
Ψ_r(t,u) ≤ 2 ψ(t) - (u-q_r)^2 / K₀
```

with the threshold defining A to get

```text
Ψ_r(t,u) ≤ 2 φ_N(t) - 2 ε₁.
```

### 6C. Apply concentration and sum over overlaps

In the Ising cube there are at most `2N+1` possible overlaps. Apply Proposition 14.5.8 termwise and sum:

```text
(2N+1) K exp(-N/K) → 0.
```

Package the result in eventual form to avoid repeatedly choosing explicit `N₀`.

### Exit criterion

A theorem matching (14.110)–(14.111), with the order of quantifiers visible in the Lean statement.

---

## Phase 7 — Theorem 14.5.4: interpolation convergence below t=1

Create `SpinGlass/Parisi/ParisiInterpolationLower.lean`.

### 7A. Exact derivative remainder

Identify the current Guerra interpolation function corresponding to Talagrand's `φ_N(t)` and the Parisi-side `ψ(t)`. Reuse existing derivative formulas.

Extract a theorem of the form:

```text
ψ'(t) - φ_N'(t)
 = E⟨ ξ(R₁₂) - R₁₂ ξ'(q(α,γ)) + θ(q(α,γ)) ⟩_t / 2
```

up to the repository's sign/normalization conventions.

### 7B. Quadratic Taylor remainder in R₁₂-q_r

Using bounded `ξ''` on `[-1,1]`, prove

```text
|ξ(R)-R ξ'(q_r)+θ(q_r)| ≤ C (R-q_r)^2.
```

### 7C. Insert localization

On the good event, `(R-q_r)^2` is bounded by `K(ψ-φ+ε₁)`; on the bad event use `|R-q_r|≤2` and the localization probability ≤ ε₁.

After summing over r, obtain eventually for all `t≤t₀`:

```text
(ψ - φ_N)'(t) ≤ K (ψ(t)-φ_N(t)+ε₁).
```

### 7D. Differential inequality

Use the existing Appendix-style differential inequality lemma (or Mathlib Grönwall if already used) and `ψ(0)-φ_N(0)=0` to show

```text
sup_{t≤t₀} (ψ(t)-φ_N(t)) ≤ C(t₀) ε₁
```

for all sufficiently large N.

Then let `ε₁ → 0` to obtain Talagrand (14.107), preferably in an eventual epsilon formulation well suited to the final theorem.

### Exit criterion

A theorem for every fixed `t₀<1` giving the required convergence/comparison at `t₀` (or uniformly on `[0,t₀]`).

---

## Phase 8 — Endpoint comparison and capstone

### 8A. Reproduce (14.109) in the repository's notation

Need a volume-uniform derivative bound:

```text
ψ'(t) - M ≤ φ_N'(t) ≤ ψ'(t)
```

for `0≤t≤1`, with M depending only on ξ (and normalization), not N.

The upper inequality is the usual Guerra direction. The lower coarse bound should follow from boundedness of overlaps/profile derivatives; prove it once as an explicit lemma.

### 8B. Pass from t₀ to 1

From Phase 7 at fixed `t₀` and the derivative bound, derive:

```text
liminf_N φ_N(1) ≥ ψ(1) - (1-t₀) M.
```

Identify endpoints:

```text
φ_N(1) = iidFieldMixedPSpinFreeEnergy N μh ξ
ψ(1)   = randomFieldParisiFunctional μh ξ ms qs.
```

Use MIN near-infimum:

```text
randomFieldParisiFunctional μh ξ ms qs ≤ randomFieldParisiInf μh ξ + ε_MIN.
```

Arrange epsilon bookkeeping so the final conclusion is the **lower** bound

```text
randomFieldParisiInf μh ξ - ε ≤ iidFieldMixedPSpinFreeEnergy N μh ξ
```

eventually. Note that because `randomFieldParisiInf ≤ P_k`, any lower bound by a MIN functional minus small errors is automatically enough.

### 8C. Fill `ParisiLowerBound.lean`

Replace the current `sorry` in:

```lean
eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy_of_nondegenerate
```

with a short assembly proof importing the modules above.

Do not expand the 3000-line proof inline.

### 8D. Preserve reductions

Recompile the already existing:

- `eventually_randomFieldParisiInf_sub_le_iidFieldMixedPSpinFreeEnergy`
- `tendsto_iidFieldMixedPSpinFreeEnergy_randomFieldParisiInf`
- `randomFieldParisiInf_le_liminf_iidFieldMixedPSpinFreeEnergy`

No extra assumptions should appear.

---

## Phase 9 — Integration, documentation, CI coverage

### 9A. Import graph

Add the new modules to the appropriate import chain. At the end add:

```lean
import SpinGlass.Parisi.ParisiLowerBound
```

(or the chosen capstone import) to `SpinGlass.lean`.

### 9B. Update docs

Update:

- `ARCHITECTURE.md`
- relevant `README.md` paragraph that currently says the lower half is still open.

### 9C. Validation

Run in this order:

```bash
lake env lean SpinGlass/Parisi/ParisiMin.lean
lake env lean SpinGlass/Parisi/ParisiMVariation.lean            # if created
lake env lean SpinGlass/Parisi/ParisiMainEstimate.lean
lake env lean SpinGlass/Parisi/ParisiConcentration.lean
lake env lean SpinGlass/Parisi/ParisiLocalization.lean
lake env lean SpinGlass/Parisi/ParisiInterpolationLower.lean
lake env lean SpinGlass/Parisi/ParisiLowerBound.lean
lake build
```

Then:

```bash
rg -n '\b(sorry|admit|axiom)\b' SpinGlass/Parisi
```

Review every hit in the new dependency cone.

---

## Expected hard points and fallback strategy

### Hard point: joint continuity in MIN

If direct joint continuity of the whole functional is painful, use finite composition:

- each Gaussian variance depends continuously on q;
- each Cole–Hopf level is jointly continuous in exponent and variance on the compact domain, with the m=0 extension already handled;
- finite iteration preserves continuity;
- integrate against μh using a uniform linear/quadratic domination coming from log-cosh bounds and the finite moment available from `NondegenerateExternalFieldLaw`.

Do not evade compact minimization by selecting an approximate q-minimizer only; later mass variations need exact minimality.

### Hard point: random external field in concentration

Condition on the full realized `hVec`. The concentration variable is the Gaussian disorder/cascade marks only. Show the Lipschitz constant is independent of `hVec`; then integrate the resulting probability/expectation inequality over `hVec`. This should avoid any exponential moment assumption on μh.

### Hard point: seven cases create too much duplication

Separate:

- **parameter construction**,
- **coupled-bound algebra**,
- **scalar calculus inequality**.

Then mirror cases can reuse the same scalar lemmas with sign/order substitutions.

### Hard point: strict far improvement → uniform quadratic bound

Do not try to manufacture a quadratic inequality pointwise. First prove strict improvement on a compact set away from `q_r`, get a positive uniform gap by compactness/continuity, then convert that fixed gap into a quadratic penalty using the bounded overlap interval.

### Hard point: endpoint epsilon bookkeeping

Use named positive quantities, not nested fractions. Suggested split for target ε:

```text
ε_MIN   = ε/4
ε_INT   = ε/4
ε_END   = ε/2
```

Choose `t₀` so `(1-t₀)M < ε_END`, choose MIN within `ε_MIN`, and choose N large enough for interpolation error `ε_INT`.

---

## Definition of done

One-shot implementation is successful when:

- `ParisiLowerBound.lean` contains no proof hole;
- no stronger field or ξ assumptions were added to the capstone;
- the Chapter 14 proof dependency is explicit and documented;
- all new files compile individually;
- `SpinGlass.lean` imports the capstone;
- `lake build` passes;
- gap/docs files are synchronized with reality.
