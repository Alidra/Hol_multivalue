require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1246909_term_abbrevs;
opaque symbol lem1246909 (m : El num) (n : El num) : Prf (= (term0 m n) (= (<= n m) (term1 m n))) ≔ REFL (term0 m n);
