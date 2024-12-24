require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516852_term_abbrevs;
opaque symbol lem516852 (m : El num) (n : El num) (p : El num) : Prf (= (term0 m n p) (= (term1 n m p) (term2 m n p))) ≔ REFL (term0 m n p);
