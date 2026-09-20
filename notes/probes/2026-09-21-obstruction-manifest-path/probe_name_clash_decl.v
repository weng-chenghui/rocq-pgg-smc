From obsprobe Require Import probe_name_clash.

Definition probe_name_clash (n : nat) := n.

Check probe_name_clash 3.
Check probe_clash_witness.
Locate probe_name_clash.
