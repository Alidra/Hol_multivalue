require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070450_term_abbrevs;
opaque symbol lem1070450 [A] (NIL' : El (recspace A)) (h1 : Prf (= NIL' (term0 A))) : Prf (= NIL' (term0 A)) ≔ h1;
