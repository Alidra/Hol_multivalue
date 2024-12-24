require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1096517_spec;
opaque symbol lem1096519 [A] : Prf (= ((@REVERSE A) (@NIL A)) (@NIL A)) ≔ ∧ₑ₁ (@lem1096517 A);
