require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm994716_spec;
opaque symbol lem994718 (n : El num) : Prf (= (* _0 n) _0) ≔ ∧ₑ₁ (@lem994716 n (@el num));
