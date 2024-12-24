require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm71260_term_abbrevs;
opaque symbol lem71260 (a : El num) : Prf (= (term0 a) a) ≔ @axiom_7 a;
