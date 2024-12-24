require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm822_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem822 (p : El bool) (q : El bool) : Prf (= (term0 p q) (= (term1 p q) (∨ p q))) ≔ (@lem32 (term1 p q) (∨ p q));
