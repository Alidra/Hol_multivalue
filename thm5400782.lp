require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5400782_term_abbrevs;
opaque symbol lem5400782 (m : El num) (p : El num) (n : El num) : Prf (= (term0 m n p) (= (term1 p m n) (term2 m p n))) ≔ REFL (term0 m n p);
