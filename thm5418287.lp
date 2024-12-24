require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418287_term_abbrevs;
require open hol-light.thm5401059_spec;
require open hol-light.thm5418283_spec;
opaque symbol lem5418287 (m : El num) (n : El num) (h1 : Prf (term0 m n)) : Prf (term1 m n) ≔ EQ_MP (@lem5401059 m n) (@lem5418283 m n h1);
