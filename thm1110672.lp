require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1110672_term_abbrevs;
require open hol-light.thm1110669_spec;
opaque symbol lem1110671 [A] : Prf (term0 A) ≔ ∧ₑ₁ (@lem1110669 A);
opaque symbol lem1110672 [A] (r : El (type1402 A)) : Prf (term1 A r) ≔ (@lem1110671 A) r;
