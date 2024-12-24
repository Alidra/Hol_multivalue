require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1069015_term_abbrevs;
opaque symbol lem1069015 [A] (NONE' : El (recspace A)) (h1 : Prf (= NONE' (term0 A))) : Prf (= NONE' (term0 A)) ≔ h1;
