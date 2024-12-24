require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm516724_term_abbrevs;
require open hol-light.thm516702_spec;
opaque symbol lem516723 : Prf term0 ≔ ∧ₑ₁ (@lem516702);
opaque symbol lem516724 (n : El num) : Prf (term1 n) ≔ (@lem516723) n;
