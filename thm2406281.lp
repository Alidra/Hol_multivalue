require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2406281_term_abbrevs;
require open hol-light.thm2406278_spec;
opaque symbol lem2406281 (m : El num) (n : El num) : Prf (= (term0 m n) (term1 n)) ≔ ∧ₑ₁ (@lem2406278 m n);
