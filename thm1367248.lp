require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1367248_term_abbrevs;
require open hol-light.thm1367246_spec;
opaque symbol lem1367248 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₁ (@lem1367246 m n);
