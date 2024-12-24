require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm994716_spec;
opaque symbol lem994717 (m : El num) : Prf (= (* m _0) _0) ≔ ∧ₑ₂ (@lem994716 (@el num) m);
