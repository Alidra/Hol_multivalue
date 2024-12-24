require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm5418284_term_abbrevs;
require open hol-light.thm5400860_spec;
require open hol-light.thm5413112_spec;
opaque symbol lem5418284 (m : El num) (n : El num) (h1 : Prf (term0 m n)) : Prf (term1 m n) ≔ (@lem5413112 m n) (@lem5400860 m n h1);
