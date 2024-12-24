require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm952_term_abbrevs;
require open hol-light.thm32_spec;
opaque symbol lem952 (q : El bool) (p : El bool) (r : El bool) : Prf (= (term0 p q r) (= (term1 p q r) (term2 q p r))) ≔ (@lem32 (term1 p q r) (term2 q p r));
