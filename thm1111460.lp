require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1111460_term_abbrevs;
require open hol-light.thm1111457_spec;
opaque symbol lem1111459 [A] : Prf (term0 A) ≔ ∧ₑ₁ (@lem1111457 A);
opaque symbol lem1111460 [A] (s : El (fun num A)) : Prf (term1 A s) ≔ (@lem1111459 A) s;
