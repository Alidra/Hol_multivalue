require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1070977_term_abbrevs;
opaque symbol lem1070977 [A] (a : El (list A)) : Prf (= (term0 A a) a) ≔ @axiom_15 A a;
