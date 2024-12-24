require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.LAST_term_abbrevs;
require open hol-light.thm1098347_spec;
require open hol-light.thm1098348_spec;
opaque symbol lem1098349 [A] (h : El A) (t : El (list A)) : Prf (= (term0 A h t) (term1 A h t)) ≔ EQ_MP (@lem1098348 A h t) (@lem1098347 A h t);
