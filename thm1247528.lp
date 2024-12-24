require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1247528_term_abbrevs;
opaque symbol lem1247528 (d' : El num) (d : El num) (n : El num) (d'' : El num) (h1 : Prf (= (term0 n d' d) (+ n d''))) : Prf (= (term0 n d' d) (+ n d'')) ≔ h1;
