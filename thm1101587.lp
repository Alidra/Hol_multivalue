require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1101587_term_abbrevs;
require open hol-light.thm1101584_spec;
opaque symbol lem1101586 [_25328] : Prf (term0 _25328) ≔ ∧ₑ₁ (@lem1101584 _25328);
opaque symbol lem1101587 [_25328] (P : El (fun _25328 bool)) : Prf (term1 _25328 P) ≔ (@lem1101586 _25328) P;
