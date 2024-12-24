require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1248167_term_abbrevs;
opaque symbol lem1248167 (d : El num) (n : El num) (p : El num) (q : El num) (d' : El num) (h1 : Prf (= (term0 p d n) (term0 p q d'))) : Prf (= (term0 p d n) (term0 p q d')) ≔ h1;
