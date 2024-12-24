require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1240294_term_abbrevs;
opaque symbol lem1240294 (r : El type1678) : Prf (= (term0 r) (= (term1 r) r)) ≔ @axiom_18 r;
