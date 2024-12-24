require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm515685_term_abbrevs;
require open hol-light.thm515633_spec;
opaque symbol lem515684 : Prf term0 ≔ ∧ₑ₁ (@lem515633);
opaque symbol lem515685 (m : El num) : Prf (term1 m) ≔ (@lem515684) m;
