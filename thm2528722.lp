require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2528722_term_abbrevs;
opaque symbol lem2528722 (m : El int) (n : El int) (p : El int) : Prf (= (term0 m n p) (= (= (rem m p) (rem n p)) (term1 m n p))) ≔ REFL (term0 m n p);
