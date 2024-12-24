require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367769_term_abbrevs;
require open hol-light.thm1367766_spec;
opaque symbol lem1367769 (m : El num) (n : El num) : Prf (= (term0 n m) (real_of_num n)) ≔ ∧ₑ₁ (@lem1367766 m n);
