require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm996238_term_abbrevs;
require open hol-light.thm996236_spec;
opaque symbol lem996238 (n : El num) : Prf (= (term0 n) n) ≔ ∧ₑ₁ (@lem996236 n (@el num));
