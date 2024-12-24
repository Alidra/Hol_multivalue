require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516896_term_abbrevs;
require open hol-light.thm516884_spec;
opaque symbol lem516895 : Prf term0 ≔ ∧ₑ₁ (@lem516884);
opaque symbol lem516896 (m : El num) : Prf (term1 m) ≔ (@lem516895) m;
