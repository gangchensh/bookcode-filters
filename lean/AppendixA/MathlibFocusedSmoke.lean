import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

open Filter
open scoped Topology

#check Filter
#check Filter.atTop
#check Filter.Tendsto
#check nhds

example {P Q : Nat → Prop}
    (hP : ∀ᶠ n in atTop, P n)
    (hQ : ∀ᶠ n in atTop, Q n) :
    ∀ᶠ n in atTop, P n ∧ Q n := by
  exact hP.and hQ
