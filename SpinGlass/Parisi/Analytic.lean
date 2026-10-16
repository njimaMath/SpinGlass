import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import SpinGlass.Parisi.Analytic.BoundedDifferences
import SpinGlass.Parisi.Analytic.Compactness
import SpinGlass.Parisi.Analytic.Concentration
import SpinGlass.Parisi.Analytic.Convexity
import SpinGlass.Parisi.Analytic.FieldTruncation
import SpinGlass.Parisi.Analytic.FinitePartition
import SpinGlass.Parisi.Analytic.Gaussian.Curvature
import SpinGlass.Parisi.Analytic.Gaussian.Differentiation
import SpinGlass.Parisi.Analytic.Gaussian.Integrability
import SpinGlass.Parisi.Analytic.Gaussian.Split
import SpinGlass.Parisi.Analytic.Heat.Backward
import SpinGlass.Parisi.Analytic.Heat.Basic
import SpinGlass.Parisi.Analytic.Heat.Jet
import SpinGlass.Parisi.Analytic.Heat.Split
import SpinGlass.Parisi.Analytic.Heat.Taylor
import SpinGlass.Parisi.Analytic.Hyperbolic
import SpinGlass.Parisi.Analytic.Infimum
import SpinGlass.Parisi.Analytic.IntegralDifferentiation
import SpinGlass.Parisi.Analytic.Interpolation
import SpinGlass.Parisi.Analytic.Lipschitz
import SpinGlass.Parisi.Analytic.Localization
import SpinGlass.Parisi.Analytic.Mass.Basic
import SpinGlass.Parisi.Analytic.Mass.Bounds
import SpinGlass.Parisi.Analytic.Mass.Derivatives
import SpinGlass.Parisi.Analytic.Profile
import SpinGlass.Parisi.Analytic.Taylor
import SpinGlass.Parisi.Analytic.Variation

/-!
# Analytic tools for the Parisi development

The topic modules under `Analytic/` contain the definitions and proofs.
Mass, Gaussian and Heat families use separate basic, calculus and estimate
owners; independent convexity and Lipschitz lemmas have their own modules.

All existing `SpinGlass.Aristotle` and `SpinGlass.Aristotle.Heat` declaration
names are preserved. Proof leaves should import the relevant topic directly.
See `Docs/ANALYTIC.md` for the complete owner map.
-/
