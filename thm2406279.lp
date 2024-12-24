require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2406279_term_abbrevs;
require open hol-light.thm2406276_spec;
opaque symbol lem2406279 (m : El num) (n : El num) : Prf (= (term0 n m) (int_of_num n)) ≔ ∧ₑ₁ (@lem2406276 m n);
