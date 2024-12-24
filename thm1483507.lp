require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1483507_term_abbrevs;
require open hol-light.thm1483505_spec;
opaque symbol lem1483507 (x : El real) (q : El num) : Prf (= (term0 x q) (term1 x q)) ≔ ∧ₑ₂ (@lem1483505 (@el real) (@el real) x q);
