Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/manifest
was previously bound to reading_index.staged.manifest; it is remapped to
pgg_smc [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/pgl27/tableau
was previously bound to reading_index.staged.instances.pgl27.tableau; it is
remapped to pgg_smc.tableau [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/pgl27
was previously bound to reading_index.staged.instances.pgl27; it is remapped
to pgg_smc [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/kim2025/tableau
was previously bound to reading_index.staged.instances.kim2025.tableau; it is
remapped to pgg_smc.tableau [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/kim2025
was previously bound to reading_index.staged.instances.kim2025; it is
remapped to pgg_smc [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/s5/tableau
was previously bound to reading_index.staged.instances.s5.tableau; it is
remapped to pgg_smc.tableau [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/s5
was previously bound to reading_index.staged.instances.s5; it is remapped to
pgg_smc [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/psl211/tableau
was previously bound to reading_index.staged.instances.psl211.tableau; it is
remapped to pgg_smc.tableau [overriding-logical-loadpath,filesystem,default]
Warning:
/Users/cheng-huiweng/Projects/coq/rocq-pgg-smc/notes/probes/2026-09-21-reading-index/index2/staged/instances/psl211
was previously bound to reading_index.staged.instances.psl211; it is remapped
to pgg_smc [overriding-logical-loadpath,filesystem,default]
File "./msg/k5_rebuild.v", line 9, characters 0-77:
Warning: Notations "_ <| _" defined at level 70 with arguments constr
at next level, constr at next level and "_ <| _ |> _" defined at level 49
with arguments constr at next level, constr at next level
have incompatible prefixes. One of them will likely not work.
[notation-incompatible-prefix,parsing,default]
File "./msg/k5_rebuild.v", line 49, characters 5-39:
Error:
In environment
R : realType
A : PGGAlgebraic
E : ExecutionParams A
sa : SampleAdapter R (instance_exec E)
w : ExactWitness sa blind_reading
The term "ew_indep (e:=w)" has type
 "forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP sa |= (fun u : sa_sampleT sa =>
                    er_of_endpoints blind_reading C
                      (static_coalition_obs C (sa_arg u) (sa_cut u))) _|_ 
  ew_secret w"
while it is expected to have type
 "forall C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1},
  (#|C| < profile_k (instance_profile A))%N ->
  sa_sampleP sa |= (fun u : sa_sampleT sa =>
                    static_coalition_obs C (sa_arg u) (sa_cut u)) _|_ 
  ew_secret w"
(cannot unify "pfwd1
                 [% fun u : sa_sampleT sa =>
                    er_of_endpoints blind_reading C
                      (static_coalition_obs C (sa_arg u) (sa_cut u)), 
                 ew_secret w] (x0, y) =
               pfwd1
                 (fun u : sa_sampleT sa =>
                  er_of_endpoints blind_reading C
                    (static_coalition_obs C (sa_arg u) (sa_cut u)))
                 x0 *
               pfwd1 (ew_secret w) y"
and
"pfwd1
   [% fun u : sa_sampleT sa => static_coalition_obs C (sa_arg u) (sa_cut u), 
   ew_secret w] (x0, y) =
 pfwd1
   (fun u : sa_sampleT sa => static_coalition_obs C (sa_arg u) (sa_cut u)) x0 *
 pfwd1 (ew_secret w) y").

