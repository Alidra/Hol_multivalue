require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066989_term_abbrevs;
opaque symbol lem1066989 [A B] (r : El (type1677 A B)) : Prf (= (term0 A B r) (= (term1 A B r) r)) ≔ @axiom_12 A B r;
