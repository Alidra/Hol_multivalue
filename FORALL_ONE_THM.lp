require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FORALL_ONE_THM_term_abbrevs;
require open hol-light.thm16264_spec;
require open hol-light.thm16265_spec;
opaque symbol lem16266 (P : El (fun 1 bool)) : Prf (= (term0 P) (P one)) ≔ EQ_MP (@lem16265 P) (@lem16264 P);
