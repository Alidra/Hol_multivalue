require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm4785464_spec;
opaque symbol lem4785466 [A] : Prf (= ((@set_of_list A) (@NIL A)) (@EMPTY A)) ≔ ∧ₑ₁ (@lem4785464 A);
