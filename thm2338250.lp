require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2338250_term_abbrevs;
opaque symbol lem2338250 (m : El num) (n : El num) : Prf (= (term0 m n) (= (< n m) (term1 m n))) ≔ REFL (term0 m n);
