require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418289_term_abbrevs;
require open hol-light.thm5400988_spec;
require open hol-light.thm5418285_spec;
opaque symbol lem5418289 (m : El num) (h1 : Prf (term0 m)) : Prf (term1 m) ≔ EQ_MP (@lem5400988 m) (@lem5418285 m h1);
