require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm531122_term_abbrevs;
require open hol-light.thm531089_spec;
opaque symbol lem531121 : Prf term0 ≔ ∧ₑ₁ (@lem531089);
opaque symbol lem531122 (n : El num) : Prf (term1 n) ≔ (@lem531121) n;
