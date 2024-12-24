require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1318759_term_abbrevs;
require open hol-light.thm1318748_spec;
opaque symbol lem1318758 : Prf term0 ≔ ∧ₑ₁ (@lem1318748);
opaque symbol lem1318759 (P : El (fun hreal bool)) : Prf (term1 P) ≔ (@lem1318758) P;
