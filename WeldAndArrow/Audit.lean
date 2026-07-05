import WeldAndArrow.Invariance

namespace WAA

/--
info: 'WAA.no_agent_recovery_of_field_collision' does not depend on any axioms
-/
#guard_msgs in
#print axioms no_agent_recovery_of_field_collision

/--
info: 'WAA.DirectionNegative.no_direction_recovery_from_conditionsEither' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms DirectionNegative.no_direction_recovery_from_conditionsEither

/--
info: 'WAA.Grid.stateToolFits_iff_atBot' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.stateToolFits_iff_atBot

/--
info: 'WAA.Grid.map_actual_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_actual_iff

/--
info: 'WAA.Grid.map_isShareDrop_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.map_isShareDrop_iff

/--
info: 'WAA.Grid.DirectedConvention.map_landsWithShareDrop_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.map_landsWithShareDrop_iff

/--
info: 'WAA.Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff' does not depend on any axioms
-/
#guard_msgs in
#print axioms Grid.DirectedConvention.BeingConvention.BeingCoarsening.map_selfConditioningTag_iff

end WAA
