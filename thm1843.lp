require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1843_term_abbrevs;
require open hol-light.thm1842_spec;
opaque symbol lem1843 (t : El bool) : Prf (term0 t) ≔ ∧ₑ₂ (@lem1842 t);
