require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483482_term_abbrevs;
require open hol-light.thm1483479_spec;
opaque symbol lem1483482 (a : El real) (b : El real) (c : El real) : Prf (= (term0 a b c) (term1 a b c)) ≔ ∧ₑ₁ (@lem1483479 b a c (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
