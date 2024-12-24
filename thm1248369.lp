require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1248369_term_abbrevs;
opaque symbol lem1248369 (n : El num) (m : El num) (d : El num) (q : El num) (d' : El num) (h1 : Prf (= (+ m n) (term0 m d q d'))) : Prf (= (+ m n) (term0 m d q d')) ≔ h1;
