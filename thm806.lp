require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm804_spec;
require open hol-light.thm805_spec;
opaque symbol lem806 (p : El bool) : Prf (= (∨ p p) p) ≔ EQ_MP (@lem805 p) (@lem804 p);
