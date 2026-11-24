(* Re-run independently with [make audit]; every result should be closed. *)
From DAnalyzer.Abstract Require Import TransitionSound.
From DAnalyzer.Examples Require Import Examples.
From DAnalyzer.Examples Require Import NonLatticeDomain.

Print Assumptions iterate_chain.
Print Assumptions kleene_lfp.
Print Assumptions iterate_sound.
Print Assumptions iteration_limit_sound.
Print Assumptions lfp_least.
Print Assumptions lfp_fixed.
Print Assumptions union_sharp_mono.
Print Assumptions gamma_union_left.
Print Assumptions lookup_sound.
Print Assumptions lookup_complete.
Print Assumptions lookup_cmd_none.
Print Assumptions continuation_valid.
Print Assumptions next_valid.
Print Assumptions nextTrue_valid.
Print Assumptions nextFalse_valid.
Print Assumptions step_points.
Print Assumptions Reach_finite.
Print Assumptions Reach_kleene.
Print Assumptions Reach_points.
Print Assumptions state_galois.
Print Assumptions partition_join.
Print Assumptions local_step_mono.
Print Assumptions Step_sharp_mono.
Print Assumptions Reach_sharp_fixed.
Print Assumptions local_simulation.
Print Assumptions Step_sound.
Print Assumptions invariant_sound.
Print Assumptions reachability_sound.
Print Assumptions alpha_reachability_sound.
Print Assumptions no_cross_memory_assignment.
Print Assumptions aliased_store.
Print Assumptions nested_lexical_context.
Print Assumptions nested_successors.
Print Assumptions goto_has_no_static_successor.
Print Assumptions invalid_goto.
Print Assumptions interior_jump_has_no_return.
Print Assumptions true_loop_no_final_memory.
Print Assumptions update_distinct_variables.
Print Assumptions name_code_injective.
Print Assumptions integer_dereference.
Print Assumptions integer_store.
Print Assumptions fork_no_common_upper.
Print Assumptions fork_union_is_not_an_upper_bound.
Print Assumptions nonlattice_soundness.
