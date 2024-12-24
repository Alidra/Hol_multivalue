require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1247563_term_abbrevs;
opaque symbol lem1247563 (d' : El num) (m : El num) (d : El num) (d'' : El num) (h1 : Prf (= (+ m d') (term0 m d d''))) : Prf (= (+ m d') (term0 m d d'')) ≔ h1;
