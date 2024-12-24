require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1247628_term_abbrevs;
opaque symbol lem1247628 (p : El num) (q : El num) (m : El num) (n : El num) (d : El num) (h1 : Prf (= (+ p q) (term0 m n d))) : Prf (= (+ p q) (term0 m n d)) ≔ h1;
