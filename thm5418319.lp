require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418319_term_abbrevs;
require open hol-light.thm5418304_spec;
opaque symbol lem5418319 (m : El num) : Prf (term0 m) ≔ λ n : El num, (@lem5418304 m n);
