require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1247613_term_abbrevs;
opaque symbol lem1247613 (m : El num) (n : El num) (p : El num) (q : El num) (d : El num) (h1 : Prf (= (+ m n) (term0 p q d))) : Prf (= (+ m n) (term0 p q d)) ≔ h1;
