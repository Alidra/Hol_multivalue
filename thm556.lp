require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm554_spec;
require open hol-light.thm555_spec;
opaque symbol lem556 (q : El bool) (p : El bool) : Prf (= (∧ p q) (∧ q p)) ≔ EQ_MP (@lem555 q p) (@lem554 p q);
