require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2406277_term_abbrevs;
require open hol-light.thm2406274_spec;
opaque symbol lem2406277 (m : El num) (n : El num) : Prf (= (term0 n m) (term1 n)) ≔ ∧ₑ₁ (@lem2406274 m n);
