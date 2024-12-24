require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070978_term_abbrevs;
opaque symbol lem1070978 [A] (r : El (recspace A)) : Prf (= (term0 A r) (= (term1 A r) r)) ≔ @axiom_16 A r;
