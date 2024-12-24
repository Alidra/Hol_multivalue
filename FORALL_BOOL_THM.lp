require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FORALL_BOOL_THM_term_abbrevs;
require open hol-light.thm11004_spec;
require open hol-light.thm11005_spec;
opaque symbol lem11006 (P : El (fun bool bool)) : Prf (= (term0 P) (term1 P)) ≔ EQ_MP (@lem11005 P) (@lem11004 P);
