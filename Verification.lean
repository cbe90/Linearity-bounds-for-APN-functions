module

-- The module interface hides theorem bodies; inspect the full declarations.
import all Solution
import Lean.Util.CollectAxioms

open Lean Elab Command

run_cmd do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let results : Array Name := #[
    ``APNLinearity.linearity_upper_bounds,
    ``APNLinearity.linearity_bound_of_odd_dimension_and_exact_two_power,
    ``APNLinearity.ranked_walsh_coefficient_bounds,
    ``APNLinearity.second_linearity_bound_of_near_maximal_linearity,
    ``APNLinearity.linearity_bounds_of_nonplateaued_component_count]
  for name in results do
    match ← getConstInfo name with
    | .thmInfo _ => pure ()
    | _ => throwError "Expected a theorem: {name}"
    let axioms ← collectAxioms name
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "Unaccepted axiom in {name}: {axiomName}"
    logInfo m!"Checked {name}; axioms: {axioms.toList}"
