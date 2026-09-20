# Renamed identifiers: security property and security evidence (2026-09-20)

Status: AS BUILT for the identifiers (commit 77a2c84, tracker step 2.6f). The
list is for the owner's own edits of texts that cite the code. No `.tex` file
was edited, and git history was left as it is, by the owner's decision.

The owner barred two nouns: the one that named a constructor of the
framework's sum type of a program's witness or certificate, and "port" for that
sum type. Neither got a synonym; each identifier says what the thing is. The
three constructors name SECURITY PROPERTIES (exact independence, input
indistinguishability, ideal proximity), and the sum type holds a program's
SECURITY EVIDENCE for one of them.

## What a citing text has to change

Nothing today: a scan on 2026-09-20 of `paper/`, `paper-wadt2026/`,
`paper-wadt2026-baseline-application/`, `blueprint/` and `README.md`, with and
without the LaTeX escape of the underscore, finds none of the 36 old names.
In a paper's prose: "the program certifies input indistinguishability", "its
security evidence is an input-indistinguishability certificate", "the program's
security property" for the value `security_property_of` returns.

## File

`manifest/pgg_tableau_arm_relations.v` is now
`manifest/pgg_tableau_security_property_relations.v`.

## Identifiers (36 names)

| Old | New | Uses |
|---|---|---|
| `ExactIndependenceArm` | `ExactIndependenceProperty` | 9 |
| `IdealProximityArm` | `IdealProximityProperty` | 7 |
| `InputIndistinguishabilityArm` | `InputIndistinguishabilityProperty` | 12 |
| `PortProp` | `EvidenceProp` | 5 |
| `SecurityArm` | `SecurityProperty` | 5 |
| `SecurityPort` | `SecurityEvidence` | 7 |
| `ab_arm` | `ab_security_property` | 10 |
| `ab_port` | `ab_evidence` | 10 |
| `certify_exact_armE` | `certify_exact_propertyE` | 4 |
| `certify_idealproximity_armE` | `certify_idealproximity_propertyE` | 2 |
| `certify_indistinguishability_armE` | `certify_indistinguishability_propertyE` | 2 |
| `conclude_armE` | `conclude_propertyE` | 3 |
| `five_card_biased_branch_indistinguishability_published_armE` | `five_card_biased_branch_indistinguishability_published_propertyE` | 2 |
| `five_card_biased_indistinguishability_published_armE` | `five_card_biased_indistinguishability_published_propertyE` | 2 |
| `five_card_biased_proximity_published_armE` | `five_card_biased_proximity_published_propertyE` | 2 |
| `five_card_biased_published_arm_neq` | `five_card_biased_published_property_neq` | 2 |
| `five_card_biased_published_inv25_armE` | `five_card_biased_published_inv25_propertyE` | 3 |
| `five_card_repeated_indistinguishability_published_armE` | `five_card_repeated_indistinguishability_published_propertyE` | 2 |
| `five_card_repeated_published39_armE` | `five_card_repeated_published39_propertyE` | 3 |
| `five_card_uniform_published_armE` | `five_card_uniform_published_propertyE` | 3 |
| `pgg_tableau_arm_relations` | `pgg_tableau_security_property_relations` | 1 |
| `pgl27_exact_published_armE` | `pgl27_exact_published_propertyE` | 3 |
| `pgl27_prior_exact_published_armE` | `pgl27_prior_exact_published_propertyE` | 3 |
| `pgl27_word_arm_is_not_exact` | `pgl27_word_property_is_not_exact` | 1 |
| `pgl27_word_branch_published39_armE` | `pgl27_word_branch_published39_propertyE` | 3 |
| `pgl27_word_proximity_published_armE` | `pgl27_word_proximity_published_propertyE` | 3 |
| `pgl27_word_published39_armE` | `pgl27_word_published39_propertyE` | 3 |
| `pgl27_word_published_armE` | `pgl27_word_published_propertyE` | 3 |
| `pgl27_word_published_arm_neq` | `pgl27_word_published_property_neq` | 3 |
| `port_arm` | `evidence_property` | 4 |
| `port_conclude` | `evidence_conclude` | 4 |
| `psl211_alldecks_published_armE` | `psl211_alldecks_published_propertyE` | 2 |
| `psl211_word_proximity_published_armE` | `psl211_word_proximity_published_propertyE` | 2 |
| `publish_armE` | `publish_propertyE` | 5 |
| `s5_rand_published_armE` | `s5_rand_published_propertyE` | 2 |
| `security_arm_of` | `security_property_of` | 29 |

How it was checked: every new name answered "No object of basename" to `Locate`
before the edit; `check_rename.py` (code tokens and comment words equal to the
parent's under the map); the reverse closure of 30 files recompiled
single-file; the two recorded `Fail` commands holding a renamed name still fail
inside the term (`notes/probes/2026-09-20-security-property-rename/`). The
comments' prose is a second, audited commit.
