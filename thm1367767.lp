require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367767_term_abbrevs;
require open hol-light.thm1367764_spec;
opaque symbol lem1367767 (m : El num) (n : El num) : Prf (= (term0 n m) (term1 n)) ≔ ∧ₑ₁ (@lem1367764 m n);
