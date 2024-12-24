require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm538284_term_abbrevs;
opaque symbol lem538284 (m : El num) (n : El num) : Prf (= (term0 m n) (= (term1 m n) (term2 m n))) ≔ REFL (term0 m n);
