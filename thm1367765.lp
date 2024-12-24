require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367765_term_abbrevs;
require open hol-light.thm1367762_spec;
opaque symbol lem1367765 (m : El num) (n : El num) : Prf (= (term0 m n) (real_of_num n)) ≔ ∧ₑ₁ (@lem1367762 m n);
