require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1337537_term_abbrevs;
require open hol-light.thm1337531_spec;
require open hol-light.thm1337536_spec;
opaque symbol lem1337537 (m : El num) : Prf (= (term0 m) (real_of_num m)) ≔ EQ_MP (@lem1337536 m) (@lem1337531 m);
