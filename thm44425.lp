require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm44425_term_abbrevs;
opaque symbol lem44425 [A B] (a : El (prod A B)) : Prf (= (term0 A B a) a) ≔ @axiom_4 A B a;
