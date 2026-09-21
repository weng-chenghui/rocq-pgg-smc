$ rocq compile <flags of _CoqProject, after> mini/k5_staged_names.v
exit status 0, 3.4 s

InputDistinguishability
     : nat
@InputDistinguishabilityPropAt
     : forall (R : reals.Real.type) (A : pgg_instance.PGGAlgebraic)
         (E : pgg_instance.ExecutionParams A),
       pgg_sample_adapter.SampleAdapter R (pgg_instance.instance_exec E) ->
       reals.Real.sort R -> Prop
InputDistinguishabilityObstruction
     : forall (R : reals.Real.type) (A : pgg_instance.PGGAlgebraic)
         (E : pgg_instance.ExecutionParams A)
         (sa : pgg_sample_adapter.SampleAdapter R
                 (pgg_instance.instance_exec E)),
       reals.Real.sort R -> ObstructionKind (E:=E) sa
ExactIndependence
     : forall (R : reals.Real.type) (A : pgg_instance.PGGAlgebraic)
         (E : pgg_instance.ExecutionParams A)
         (sa : pgg_sample_adapter.SampleAdapter R
                 (pgg_instance.instance_exec E)),
       ExactWitness (E:=E) sa -> SecurityEvidence (E:=E) sa
InputIndistinguishability
     : forall (R : reals.Real.type) (A : pgg_instance.PGGAlgebraic)
         (E : pgg_instance.ExecutionParams A)
         (sa : pgg_sample_adapter.SampleAdapter R
                 (pgg_instance.instance_exec E)),
       IndistinguishabilityCert (E:=E) sa -> SecurityEvidence (E:=E) sa
IdealProximity
     : forall (R : reals.Real.type) (A : pgg_instance.PGGAlgebraic)
         (E : pgg_instance.ExecutionParams A)
         (sa : pgg_sample_adapter.SampleAdapter R
                 (pgg_instance.instance_exec E)),
       IdealProximityCert (E:=E) sa -> SecurityEvidence (E:=E) sa
Observed
     : CompletionLevel
Sampled
     : CompletionLevel
