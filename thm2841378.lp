require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2841378_term_abbrevs;
opaque symbol lem2841378 (k : El num) (n : El num) : Prf (= (term0 k n) (= (term1 k n) (term2 k n))) ≔ REFL (term0 k n);
