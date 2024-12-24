require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm15721_term_abbrevs;
opaque symbol lem15721 (a : El 1) : Prf (= (term0 a) a) ≔ @axiom_2 a;
