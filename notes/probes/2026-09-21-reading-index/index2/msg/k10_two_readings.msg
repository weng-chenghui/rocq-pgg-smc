rocq1: waiting for the Rocq lock
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
File "./msg/k10_two_readings.v", line 8, characters 0-77:
Warning: Notations "_ <| _" defined at level 70 with arguments constr
at next level, constr at next level and "_ <| _ |> _" defined at level 49
with arguments constr at next level, constr at next level
have incompatible prefixes. One of them will likely not work.
[notation-incompatible-prefix,parsing,default]
File "./msg/k10_two_readings.v", line 34, characters 35-47:
Error:
In environment
R : realType
A : PGGAlgebraic
E : ExecutionParams A
sa : SampleAdapter R (instance_exec E)
r : EndpointReading A
r' : EndpointReading A
cert : IndistinguishabilityCert sa r'
c : R
c' : R
Hd : InputDistinguishabilityPropAt sa r c
Hp : IndistinguishabilityPropAt cert c'
C : {set 'I_(pi_T' (mp_PI (instance_profile A))).+1}
e :
  exists x x' : ex_inputT E,
    (#|C| < profile_k (instance_profile A))%N /\
    c <=
    var_dist
      (fdistmap
         (fun g : pgg_gT (mp_M (instance_profile A)) =>
          er_of_endpoints r C (static_coalition_obs C x g))
         (sa_cut_dist sa))
      (fdistmap
         (fun g : pgg_gT (mp_M (instance_profile A)) =>
          er_of_endpoints r C (static_coalition_obs C x' g))
         (sa_cut_dist sa))
x : ex_inputT E
e0 :
  exists x' : ex_inputT E,
    (#|C| < profile_k (instance_profile A))%N /\
    c <=
    var_dist
      (fdistmap
         (fun g : pgg_gT (mp_M (instance_profile A)) =>
          er_of_endpoints r C (static_coalition_obs C x g))
         (sa_cut_dist sa))
      (fdistmap
         (fun g : pgg_gT (mp_M (instance_profile A)) =>
          er_of_endpoints r C (static_coalition_obs C x' g))
         (sa_cut_dist sa))
x' : ex_inputT E
a :
  (#|C| < profile_k (instance_profile A))%N /\
  c <=
  var_dist
    (fdistmap
       (fun g : pgg_gT (mp_M (instance_profile A)) =>
        er_of_endpoints r C (static_coalition_obs C x g))
       (sa_cut_dist sa))
    (fdistmap
       (fun g : pgg_gT (mp_M (instance_profile A)) =>
        er_of_endpoints r C (static_coalition_obs C x' g))
       (sa_cut_dist sa))
HC : (#|C| < profile_k (instance_profile A))%N
Hge :
  c <=
  var_dist
    (fdistmap
       (fun g : pgg_gT (mp_M (instance_profile A)) =>
        er_of_endpoints r C (static_coalition_obs C x g))
       (sa_cut_dist sa))
    (fdistmap
       (fun g : pgg_gT (mp_M (instance_profile A)) =>
        er_of_endpoints r C (static_coalition_obs C x' g))
       (sa_cut_dist sa))
The term "Hp C x x' HC" has type
 "is_true
    (var_dist
       (fdistmap
          (fun g : pgg_gT (mp_M (instance_profile A)) =>
           er_of_endpoints r' C (static_coalition_obs C x g))
          (sa_cut_dist sa))
       (fdistmap
          (fun g : pgg_gT (mp_M (instance_profile A)) =>
           er_of_endpoints r' C (static_coalition_obs C x' g))
          (sa_cut_dist sa)) <=
     c')"
while it is expected to have type
 "is_true
    (var_dist
       (fdistmap
          (fun g : pgg_gT (mp_M (instance_profile A)) =>
           er_of_endpoints r C (static_coalition_obs C x g))
          (sa_cut_dist sa))
       (fdistmap
          (fun g : pgg_gT (mp_M (instance_profile A)) =>
           er_of_endpoints r C (static_coalition_obs C x' g))
          (sa_cut_dist sa)) <=
     ?z)".

