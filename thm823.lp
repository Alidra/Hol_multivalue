require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm823_term_abbrevs;
require open hol-light.thm821_spec;
require open hol-light.thm822_spec;
opaque symbol lem823 (p : El bool) (q : El bool) : Prf (= (term0 p q) (∨ p q)) ≔ EQ_MP (@lem822 p q) (@lem821 p q);
