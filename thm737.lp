require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm735_spec;
require open hol-light.thm736_spec;
opaque symbol lem737 (q : El bool) (p : El bool) : Prf (= (∨ p q) (∨ q p)) ≔ EQ_MP (@lem736 q p) (@lem735 p q);
