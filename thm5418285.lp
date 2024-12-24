require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418285_term_abbrevs;
require open hol-light.thm5400825_spec;
require open hol-light.thm5405853_spec;
opaque symbol lem5418285 (m : El num) (h1 : Prf (term0 m)) : Prf (term1 m) ≔ (@lem5405853 m) (@lem5400825 m h1);
