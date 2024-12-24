require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EQ_REFL_term_abbrevs;
opaque symbol lem299 [A] (x : El A) : Prf (= x x) ≔ REFL x;
opaque symbol lem304 [A] : Prf (term0 A) ≔ λ x : El A, (@lem299 A x);
