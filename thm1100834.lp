require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1100834_term_abbrevs;
require open hol-light.thm1100831_spec;
opaque symbol lem1100833 [_25307] : Prf (term0 _25307) ≔ ∧ₑ₁ (@lem1100831 _25307);
opaque symbol lem1100834 [_25307] (P : El (fun _25307 bool)) : Prf (term1 _25307 P) ≔ (@lem1100833 _25307) P;
