require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982745_term_abbrevs;
require open hol-light.thm1982742_spec;
opaque symbol lem1982745 (lx : El real) (ly : El real) (rx : El real) : Prf (= (term0 lx ly rx) (term1 lx ly rx)) ≔ ∧ₑ₁ (@lem1982742 ly rx lx (@el real) (@el real) (@el real) (@el real) (@el real) (@el num) (@el real) (@el real) (@el real) (@el num));
