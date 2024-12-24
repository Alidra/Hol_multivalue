require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm161351_term_abbrevs;
require open hol-light.thm159520_spec;
require open hol-light.thm160343_spec;
opaque symbol lem161351 (m : El num) (n : El num) (h1 : Prf (term0 n)) : Prf (= (term1 m n) m) ≔ EQ_MP (@lem159520 n m) (@lem160343 m n h1);
