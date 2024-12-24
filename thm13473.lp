require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm13473_term_abbrevs;
require open hol-light.COND_ELIM_THM_spec;
opaque symbol lem13473 [A] (_474 : El A) (_475 : El bool) (_476 : El (fun A bool)) (_477 : El A) : Prf (= (term0 A _476 _475 _474 _477) (term1 A _474 _475 _476 _477)) ≔ (@lem13472 A _474 _475 _476 _477);
