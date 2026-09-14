(* The assumption record of the Tableau surface at the PGL(2,7) instance,
   2026-09-14. Compiled from the repository root with

     rocq compile $(grep '^-R' _CoqProject | tr '\n' ' ') \
       notes/probes/2026-09-14/print_assumptions_tableau.v

   and its stdout saved beside it as print_assumptions_tableau.txt.

   The algebra, the observed execution it derives and the correctness of the
   run are closed under the global context: nothing in the executable core of
   this instance rests on an axiom. Everything that speaks about a coalition
   in a probability model carries the three classical axioms of boolp, which
   is the repository baseline and not a cost of this instance. *)

From mathcomp Require Import ssreflect.
From pgg_smc Require Import pgg_instance pgg_functionality.
From pgg_smc Require Import pgl27_secrecy pgl27_exec pgl27_rows.

Print Assumptions pgl27_algebra.
Print Assumptions pgl27_observed.
Print Assumptions pgl27_exec_correct.
Print Assumptions pgl27_dealt.
Print Assumptions pgl27_row_exact_tableau.
Print Assumptions pgl27_row_word_tableau.
Print Assumptions pgl27_exact_leak4.
Print Assumptions pgl27_exact_view_secrecy.
Print Assumptions pgl27_word_view_indist_restated.
