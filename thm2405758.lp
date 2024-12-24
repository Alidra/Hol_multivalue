require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2405758_term_abbrevs;
require open hol-light.thm2405756_spec;
opaque symbol lem2405758 (m : El num) (n : El num) : Prf (term0 m n) ≔ ∧ₑ₁ (@lem2405756 m n);
