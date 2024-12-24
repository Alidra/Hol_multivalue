require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1982777_term_abbrevs;
require open hol-light.thm1982774_spec;
opaque symbol lem1982777 (x : El real) : Prf (= (term0 x) term1) ≔ ∧ₑ₁ (@lem1982774 (@el real) (@el real) x (@el num));
