require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EXISTS_REFL_term_abbrevs;
private symbol lem4357 [A] (a : El A) : Prf (= a a) ≔ REFL a;
opaque symbol lem4358 [A] (a : El A) : Prf (term0 A a) ≔ ∃ᵢ (term1 A a) a (@lem4357 A a);
opaque symbol lem4363 [A] : Prf (term2 A) ≔ λ a : El A, (@lem4358 A a);
