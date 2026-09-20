(* Probe, 2026-09-21. Question: may a file be named after a constant declared
   in a file that requires it?

   The new file instances/psl211/psl211_alldecks_input_distinguishability.v
   carries the raw inequality, and the theorem
   psl211_alldecks_input_distinguishability stays in psl211_reading_constancy.v,
   which requires that file. So a library name and a constant name coincide in
   one scope. This probe reproduces the shape at two removes: the declaring
   file, and a third file that requires the declaring file and so sees both
   names at once. *)

Definition probe_clash_witness := 0.
