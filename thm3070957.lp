require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3070957_term_abbrevs;
require open hol-light.thm2954598_spec;
opaque symbol lem3070957 (m : El num) (n : El num) : Prf (= (term0 m n) (= (= (int_of_num m) (int_of_num n)) (= (term1 m) (term1 n)))) ≔ (@lem2954598 (= (= (int_of_num m) (int_of_num n)) (= (term1 m) (term1 n))));
