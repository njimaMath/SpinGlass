# External fields in the Parisi development

The external field is specified by a probability law `μh : Measure ℝ`. Its site
coordinates have product law `externalFieldVecLaw N μh`. The Gaussian interaction
and cascade marks are sampled independently of that vector. Every replica of a
quenched system uses the same realized vector.

For the free energy and the Parisi functional, the moment assumption is
`Integrable (fun h : ℝ => h) μh`, equivalently a finite first absolute moment.
There is no Gaussian assumption on `μh`. Degenerate laws are allowed, including
zero field. The nondegeneracy assumption used in the overlap-minimizer results
is separate and is recorded in `NondegenerateExternalFieldLaw`.

| Interface | Role |
| --- | --- |
| `siteExternalFieldEnergy` | Field energy conditional on a realized site vector |
| `siteFieldMixedPSpinFreeEnergy` | Free energy conditional on that vector |
| `iidFieldMixedPSpinFreeEnergy`, `iidFieldSKFreeEnergy` | Quenched free energy integrated over the i.i.d. site vector |
| `randomFieldParisiX₀`, `randomFieldParisiFunctional` | One-site Parisi recursion with the outer expectation over `μh` |
| `randomFieldParisiSet`, `randomFieldParisiInf` | Admissible functional values and their infimum |
| `sharedReplicaSiteField` | Embed a site vector into the two-replica field interface |
| `randomFieldPairSiteY₀`, `randomFieldPairSiteY₀'` | Coupled one-site expectation and averaged derivative, using the same field in both replicas |

The branch Hamiltonians, Ising site factorization, cascade endpoint, Gibbs pair
averages, and Guerra interpolation accept realized vectors `h : Fin N → ℝ`.
Their statements are conditional on the field realization. Integrating their
site sums against `externalFieldVecLaw` gives the law-level functional through
`integral_siteAverage_parisiFunctional`. The finite-volume i.i.d. Guerra bound
and its SK specialization allow repeated positive Parisi exponents.

The coupled interpolation already accepts a realized field
`a : Fin N × Fin 2 → ℝ`. Its site factorization and coupling bounds also have
general vector forms. For replicas of the same system, use
`a = sharedReplicaSiteField hVec`. Scalar `h : ℝ` and one-site
`h : Fin 2 → ℝ` in recursion lemmas denote conditional field values.
`randomField_coupling_rhs_zero_eq` and
`hasDerivAt_randomFieldPairSiteY₀_coupling_zero` supply their quenched
zero-coupling versions. The general differentiation-under-the-field-integral
lemma states its integrability hypothesis explicitly.

Constant fields are special cases of the i.i.d. model with `μh = Measure.dirac h`.
The free energy, Parisi functional, coupled expectation, and variational
infimum have simplification theorems for these laws. Existing scalar
finite-volume Guerra theorems specialize the vector argument.

The older theorems named `integral_mixedPSpinFreeEnergy_le_...` average a single
spatially constant field. They are retained as constant-field statements.
For the i.i.d. site model, use the theorems named
`iidFieldMixedPSpinFreeEnergy_le_...` instead.

The law-level infimum bounds any convergent sequence of i.i.d. free energies.
The theorem about such a limit explicitly requires convergence; it does not
assert existence of a thermodynamic limit for a general field law.
