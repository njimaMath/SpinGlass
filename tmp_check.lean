import SpinGlass.GuerraToninelli

namespace SpinGlass

noncomputable section

open MeasureTheory

variable {Ω : Type*} [MeasureSpace Ω]
variable (ℙ : Measure Ω)

-- try applying a function with named implicit argument inside parentheses
#check (fun {α : Type} => α) (α := Nat)

end
