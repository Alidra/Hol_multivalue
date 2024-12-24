require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.ZRECSPACE_RULES_spec;
opaque symbol lem1058929 [A] : Prf ((@ZRECSPACE A) (@ZBOT A)) ≔ ∧ₑ₁ (@lem1058926 A);
