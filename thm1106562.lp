require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1106562_term_abbrevs;
require open hol-light.thm1106559_spec;
opaque symbol lem1106561 [_25594] : Prf (term0 _25594) ≔ ∧ₑ₁ (@lem1106559 _25594);
opaque symbol lem1106562 [_25594] (P : El (fun _25594 bool)) : Prf (term1 _25594 P) ≔ (@lem1106561 _25594) P;
