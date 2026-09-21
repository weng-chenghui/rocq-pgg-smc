$ rocq compile <flags of _CoqProject, before> mini/k2_property_names.v
exit status 0, 5.4 s

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
rocq1: waiting for the Rocq lock
