# Economic-metaphor words in the FROZEN files (not edited)

Scan word list: spend/price/currency/pay/cost/earn/buy/budget/afford/
cheap/expensive/charge/bill/debt/owe/invest and inflections, inside
comments only.  The sentences below are reproduced UNCHANGED.

## `protocol/pgg_instance.v` (14)

- `protocol/pgg_instance.v:19` <cheaper>

  ```
  (* and a second is replaced by a cheaper equivalent. generic_static_recon     *)
  ```
- `protocol/pgg_instance.v:23` <owes>

  ```
  (* pga_coordE, so a dealer-dealt instance owes no reconstruction proof at     *)
  ```
- `protocol/pgg_instance.v:25` <cheaper>

  ```
  (* and only makes it cheaper: it carries the endpoint equation from a         *)
  ```
- `protocol/pgg_instance.v:28` <costly>

  ```
  (* of a concrete dealt card that makes that costly, or impossible where an    *)
  ```
- `protocol/pgg_instance.v:54` <owes>

  ```
  (* What an instance owes is termination, instance_terminates_stmt, which has  *)
  ```
- `protocol/pgg_instance.v:303` <budget>

  ```
    ex_expected : ex_inputT -> pga_secretT A ;
    (* ex_fuel is the interpreter budget. Replacing a sufficient budget by
       another sufficient one leaves every statement below unchanged. *)
  ```
- `protocol/pgg_instance.v:303` <budget>

  ```
    ex_expected : ex_inputT -> pga_secretT A ;
    (* ex_fuel is the interpreter budget. Replacing a sufficient budget by
       another sufficient one leaves every statement below unchanged. *)
  ```
- `protocol/pgg_instance.v:315` <budget>

  ```
     readout and fuel. Four of the six fields reach the plug, ex_inputT as its
     run argument type and ex_content, ex_commits and ex_fuel as its readout,
     process list and budget. ex_content_obs and ex_expected do not, because they
     are not execution data, and they enter at instance_observed. Routing the
  ```
- `protocol/pgg_instance.v:365` <owes>

  ```
     facts. This is the value every downstream analysis consumes, so supplying
     an algebra, a parameter record and the three proofs is the whole of what
     an instance owes the framework. *)
  ```
- `protocol/pgg_instance.v:691` <owes>

  ```
  (* The reconstruction obligation of an input-family run, discharged from the
     sharing claim written in its own parameter statement. Every argument occurs
     in the conclusion, so such a run owes no reconstruction proof beyond the
     encoding it already named. *)
  ```
- `protocol/pgg_instance.v:709` <owed>

  ```
  (* The eight arguments of encoded_input_params occur in the statement the
     obligation is made about, so the lemma is written unapplied where the
     obligation is owed. *)
  ```
- `protocol/pgg_instance.v:756` <costs>

  ```
     abstract-readout equation. Instantiating the variable readout at
     dealt_content gives the dealt direct computation by conversion, so the
     instance-level statement costs no reduction of its own. *)
  ```
- `protocol/pgg_instance.v:765` <costs>

  ```
     off the same abstract-readout equation. The profile statement already
     quantifies over the content readout, so instantiating it at the supplied
     layout costs the run no reduction of its own, and the two modes of the
     sharing family share the profile's one decision. *)
  ```
- `protocol/pgg_instance.v:800` <spent>

  ```
     commit-mode equation and the single fact that decoding the payload list
     returns the input the committers hold. That decoding fact is the whole of
     what an instance adds: the reduction is spent once at the profile, and this
     lemma is what turns the layout the dealer assembled from the payloads into
  ```

## `instances/psl211/psl211_exec.v` (12)

- `instances/psl211/psl211_exec.v:15` <budget>

  ```
  (* input, and the interpreter budget is psl211_fuel.  Of the three run facts  *)
  ```
- `instances/psl211/psl211_exec.v:16` <owes>

  ```
  (* it owes termination alone, decided by reduction at fuel 220 in 0.49 s of   *)
  ```
- `instances/psl211/psl211_exec.v:18` <spends>

  ```
  (* removed); reconstruction follows from the coordinate law and spends no     *)
  ```
- `instances/psl211/psl211_exec.v:35` <budget>

  ```
  (*   psl211_fuel         == the interpreter budget of the fourteen-process    *)
  ```
- `instances/psl211/psl211_exec.v:44` <budget>

  ```
  (*                              inside the budget                             *)
  ```
- `instances/psl211/psl211_exec.v:99` <budget>

  ```
  (** psl211_fuel — the interpreter budget of the fourteen-process run: the
      dealer, the verifier and the twelve seats.  220 steps, the budget the
  ```
- `instances/psl211/psl211_exec.v:100` <budget>

  ```
  (** psl211_fuel — the interpreter budget of the fourteen-process run: the
      dealer, the verifier and the twelve seats.  220 steps, the budget the
      eight-card instance uses.  The value has only to exceed the number of
  ```
- `instances/psl211/psl211_exec.v:103` <budget>

  ```
      eight-card instance uses.  The value has only to exceed the number of
      communication rounds: the interpreter halts once no process advances, so
      a budget past that number is never spent, and that 220 exceeds it is
      decided by reduction, not by counting rounds. *)
  ```
- `instances/psl211/psl211_exec.v:103` <spent>

  ```
      eight-card instance uses.  The value has only to exceed the number of
      communication rounds: the interpreter halts once no process advances, so
      a budget past that number is never spent, and that 220 exceeds it is
      decided by reduction, not by counting rounds. *)
  ```
- `instances/psl211/psl211_exec.v:109` <budget>

  ```
  (** psl211_dealt_params — the run-level data of a run that deals the
      chirality bit and recovers it: the run argument is the secret itself, no
      party commits an input, and the interpreter budget is psl211_fuel.  The
      dealer-dealt mode is what leaves the instance owing termination alone
  ```
- `instances/psl211/psl211_exec.v:116` <spent>

  ```
  (** psl211_dealt_recon — the reconstruction obligation, derived by the
      framework from the coordinate law alone.  No reduction is spent. *)
  ```
- `instances/psl211/psl211_exec.v:121` <budget>

  ```
  (** psl211_dealt_terminates — every process of the dealer-dealt run reaches
      Finish inside that budget.  The reduction is symbolic in the cut, so it
      does not enumerate the group. *)
  ```

## `instances/psl211/psl211_profile.v` (6)

- `instances/psl211/psl211_profile.v:78` <price>

  ```
      at variation distance zero from uniform, not merely close to it.  This is
      the exact certificate the bundle below carries: at one card position the
      idealised shuffle has no error to price, so every epsilon in this
      instance's marginal layer is zero and the only price paid anywhere is the
  ```
- `instances/psl211/psl211_profile.v:79` <price>

  ```
      the exact certificate the bundle below carries: at one card position the
      idealised shuffle has no error to price, so every epsilon in this
      instance's marginal layer is zero and the only price paid anywhere is the
      2^-40 of psl211_word_mixing for the realistic word shuffle. *)
  ```
- `instances/psl211/psl211_profile.v:79` <paid>

  ```
      the exact certificate the bundle below carries: at one card position the
      idealised shuffle has no error to price, so every epsilon in this
      instance's marginal layer is zero and the only price paid anywhere is the
      2^-40 of psl211_word_mixing for the realistic word shuffle. *)
  ```
- `instances/psl211/psl211_profile.v:102` <price>

  ```
      the uniform shuffle distribution and its per-position bound. Word
      length 0 records that this model does no word shuffling at all: the
      cut is drawn from the group itself, and the price of that idealisation
      is paid by psl211_word_mixing, not here. *)
  ```
- `instances/psl211/psl211_profile.v:103` <paid>

  ```
      length 0 records that this model does no word shuffling at all: the
      cut is drawn from the group itself, and the price of that idealisation
      is paid by psl211_word_mixing, not here. *)
  ```
- `instances/psl211/psl211_profile.v:132` <buys>

  ```
      Two-transitivity buys the single-card marginal above and nothing
      about this threshold. *)
  ```

## `instances/psl211/psl211_endpoints.v` (5)

- `instances/psl211/psl211_endpoints.v:6` <cost>

  ```
  (* One declaration, alone in its own file.  Compiling it on 2026-09-15 cost   *)
  ```
- `instances/psl211/psl211_endpoints.v:10` <Budget>

  ```
  (* termination lemma, reported 17.15 GB.  Budget 17 GB on a 32 GB machine.    *)
  ```
- `instances/psl211/psl211_endpoints.v:11` <cost>

  ```
  (* The cost is the twelve-card, fourteen-process interpreter trace and not    *)
  ```
- `instances/psl211/psl211_endpoints.v:12` <budget>

  ```
  (* the budget: the same reduction at fuel 380 measured 562 s and 343 s, a     *)
  ```
- `instances/psl211/psl211_endpoints.v:15` <cost>

  ```
  (* finish at any per-element cost.                                            *)
  ```

## `protocol/pgg_algebra_syntax.v` (3)

- `protocol/pgg_algebra_syntax.v:41` <spends>

  ```
  (* The block spends four identifiers as global keywords in every file that    *)
  ```
- `protocol/pgg_algebra_syntax.v:83` <owes>

  ```
     It is the map a block writes into pga_monodromy, and the reason an instance
     in this surface owes no relation between share indices and cards beyond the
     share count itself. *)
  ```
- `protocol/pgg_algebra_syntax.v:150` <buys>

  ```
     The three equations are the whole content: the result is the scheme
     unchanged, and what the combinator buys is that a block naming a different
     encoding from the scheme's own is rejected where it is written. *)
  ```

## `reconstruct/algebraic_rigidity.v` (2)

- `reconstruct/algebraic_rigidity.v:194` <budget>

  ```
  (* The cs_gap field of [tw_covering] (ts_T <= ts_k + 2 * cd_genus,
     from cover_tradeoff.v:gap_bound) is a privacy-vs-reveal gap, not
     a dropout-tolerance budget. Reconstruction in every concrete
     threshold scheme used here consumes the FULL share tuple:
  ```
- `reconstruct/algebraic_rigidity.v:391` <price>

  ```
      unconditionally, whichever regime ar_genus_gap_dichotomy places the
      scheme in. This is the numeric form of the threshold leg of algebraic
      rigidity: genus is not just a classification but a literal price cap on
      the gap. *)
  ```

## `security/pgg_collusion_bound.v` (2)

- `security/pgg_collusion_bound.v:161` <price>

  ```
  (** var_dist_uniform_supp — the TV distance from uniform-on-a-support-C to
      the fully uniform distribution on A is 2k / |A|, where k = |A| - |C| is
      the size of the excluded complement. This is the generic price, in TV
      distance, of shrinking a uniform distribution's support by k elements;
  ```
- `security/pgg_collusion_bound.v:468` <price>

  ```
      fully uniform, where epsilon is the DPI-derived distance to the ideal
      posterior conditional on dpi_bound, and
      2T'/N is the unconditional TV price of that ideal posterior itself
      being uniform only over the N - T' card positions the coalition has
  ```

## `groups/pgg_raag.v` (1)

- `groups/pgg_raag.v:1042` <spent>

  ```
     This is where the raag_sigmas_comm field of the mixin is spent, and it is why
     trace classes are coarser than words while still finer than deck
  ```

## `protocol/pgg_execution_plug.v` (1)

- `protocol/pgg_execution_plug.v:85` <budget>

  ```
                            -> seq (aproc pgg_dtype
                                      (pgg_data (pgg_N' (mp_M mp)).+1)) ;
      (* ep_fuel selects the interpreter evaluation budget used by exec_run.
  ```

## `protocol/pgg_session_types.v` (1)

- `protocol/pgg_session_types.v:111` <owed>

  ```
  (* Types a process's final return of data x under the empty session
     environment: every send this process owed has already been matched, so
     nothing remains to type-check downstream of it. *)
  ```

## `reconstruct/covering_scheme.v` (1)

- `reconstruct/covering_scheme.v:189` <price>

  ```
  (* The reconstruction/privacy gap ts_T - ts_k never exceeds twice the
     genus, restated in subtraction form directly from cs_gap. This is the
     CoveringScheme-level statement of the same price cap that
     algebraic_rigidity.v's ar_gap_bound exposes at the AlgebraicRigidity
  ```

## `security/pgg_security_solver.v` (1)

- `security/pgg_security_solver.v:71` <budget>

  ```
  (* Wraps solve_L_aux with a fixed fuel budget of 100: the smallest L such
     that epsilon_endpoint_rat Tg N L <= eps_n/eps_d, or None if no such L
  ```

Total: 49 occurrences in 12 frozen files.

## Addendum, 2026-09-20: the `-ing` and `-ed` forms the first scan did not expand (4)

Found by the plain-rows audit's completeness scan and a follow-up scan of the
frozen files. The editable twins of the first sentence were rewritten in fix
pass 1 ("leaves termination as the instance's only obligation among the three
run facts"); these four stay until the owner lifts the freeze.

- `instances/psl211/psl211_exec.v:110` <owing> "The dealer-dealt mode is what leaves the instance owing termination alone among the three run facts."
- `protocol/pgg_instance.v:457` <owing> "...which is what leaves such a run owing a ..."
- `protocol/pgg_instance.v:709` <owed> "...obligation is owed."
- `protocol/pgg_session_types.v:111` <owed> "every send this process owed has already been matched"
