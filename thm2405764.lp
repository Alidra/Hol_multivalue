require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2405764_term_abbrevs;
require open hol-light.thm2405763_spec;
opaque symbol lem2405764 (x : El num) : Prf (term0 x) ≔ ∧ₑ₂ (@lem2405763 x);
