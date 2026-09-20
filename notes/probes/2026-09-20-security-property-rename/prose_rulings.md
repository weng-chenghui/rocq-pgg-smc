# Main session's rulings for the fix pass (two barred nouns, prose layer)

## On the agents' own open items

| id | Ruling |
|---|---|
| R1 | `manifest/pgg_tableau.v`, docstring of `conclude`: "only the real the input-indistinguishability proposition mentions moves" is too narrow (`ConcludePayload` and `evidence_conclude` have a branch for ideal proximity too): "only the real a proposition carrying a number mentions moves, and it moves only upward". The prover checks the two branches before writing. |
| R2 | The frozen site `instances/psl211/psl211_exec.v:127` is not edited; it goes to the owner's list with the proposed wording of `prose_psl_s5.md`. |

## On the audit of the instance groups (`audit-prose-instances.md`)

All of H1 to H24 are ACCEPTED with the auditor's replacement, except as amended here.

| id | Amendment |
|---|---|
| H3, H6c | The tree's word for one application of the triangle inequality through an intermediate law is "hop", not "cross". And the one hop of the proximity side is in the certificate's closeness field, not in `idealproximity_tail`, which adds none (`ipc_close` is one comparison; the tail turns the ideal joint law into a product by the witness's independence). H6c, both files: "The proximity certificate's closeness field is one hop to the ideal, so that number is lost once, where the input-indistinguishability tail makes two hops." H3, header of the PGL(2,7) file: the same subjects ("The input-indistinguishability tail makes two hops ... The ideal-proximity proposition compares one law with one law, and the certificate carries the number itself, 2^-40."), every other clause of the header sentence kept. |
| H6a | Check the claim against `IdealProximityCert` before writing: `ipc_ideal : SampleAdapter R (instance_exec E)` is an adapter over the same execution at the same real field; if "at one index" in the old sentence means the family index `idx`, keep that meaning: "A proximity certificate holds its ideal at the same index as the model it is about". Report what "index" is there. |
| H4 | The form of kim and pgl27 everywhere: "The security property this program carries, at every real field and index, is <property>: ...". |
| H22 | Keep. |

## On the audit of the framework group

`audit-prose-framework.md`: F1 to F9, F11, F14, F15, F16, F17 are ACCEPTED with
the auditor's replacement. F5 supersedes R1 above (its sentence names both
propositions that mention a number). F12 and F13: no change.

F10, one spelling in `manifest/pgg_tableau_security_property_relations.v`: the
proposition is "the ideal-proximity proposition" file-wide (the property's name
is ideal proximity, and `manifest/pgg_tableau.v` uses that form and no other);
the six untouched "the proximity proposition" of that file change with it.
"the proximity certificate" and "the proximity number" stay: they name
`IdealProximityCert` and its `ipc_eps`, not the proposition. Elsewhere in the
tree the short form of the proposition stays where a whole docstring or section
already uses it consistently (H10 keeps the five-card docstring's short form).
