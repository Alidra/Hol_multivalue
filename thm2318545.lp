require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2318545_term_abbrevs;
opaque symbol lem2318545 (n : El num) : Prf (= (term0 n) (= (term1 n) (real_of_num n))) ≔ REFL (term0 n);
