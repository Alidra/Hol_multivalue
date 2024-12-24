require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070451_term_abbrevs;
opaque symbol lem1070451 [A] (CONS' : El (type1399 A)) (h1 : Prf (= CONS' (term0 A))) : Prf (= CONS' (term0 A)) ≔ h1;
