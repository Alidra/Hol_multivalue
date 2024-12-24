require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1069016_term_abbrevs;
opaque symbol lem1069016 [A] (SOME' : El (type1432 A)) (h1 : Prf (= SOME' (term0 A))) : Prf (= SOME' (term0 A)) ≔ h1;
