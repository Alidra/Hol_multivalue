require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
opaque symbol lem1247290 (p : El num) (d : El num) (n : El num) (d' : El num) (h1 : Prf (= (+ p d) (+ n d'))) : Prf (= (+ p d) (+ n d')) ≔ h1;
