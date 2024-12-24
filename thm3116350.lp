require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3116350_term_abbrevs;
opaque symbol lem3116350 (n : El num) (m : El num) : Prf (= (term0 m n) (= (= m n) (term1 n m))) ≔ REFL (term0 m n);
