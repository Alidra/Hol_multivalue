require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm2307041_term_abbrevs;
require open hol-light.thm2307014_spec;
require open hol-light.thm2307040_spec;
opaque symbol lem2307041 : Prf term0 ≔ ∧ᵢ (@lem2307040) (@lem2307014);
