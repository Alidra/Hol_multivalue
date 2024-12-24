require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1482702_term_abbrevs;
require open hol-light.thm1482701_spec;
opaque symbol lem1482702 (x : El real) (a : El real) (b : El real) (y : El real) (c : El real) (r : El real) : Prf (term0 x a b y c r) ≔ ∧ₑ₂ (@lem1482701 x a b y c r);
