require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1248182_term_abbrevs;
opaque symbol lem1248182 (q : El num) (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= (+ p q) (term0 p d n d'))) : Prf (= (+ p q) (term0 p d n d')) ≔ h1;
