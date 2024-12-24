require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm555_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem555 (q : El bool) (p : El bool) : Prf (= (term0 p q) (= (∧ p q) (∧ q p))) ≔ (@lem32 (∧ p q) (∧ q p));
