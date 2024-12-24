require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3073386_term_abbrevs;
opaque symbol lem3073386 (m : El num) (n : El num) : Prf (= (term0 m n) (= (= m n) (= (int_of_num m) (int_of_num n)))) ≔ REFL (term0 m n);
