require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EXISTS_ONE_REP_term_abbrevs;
opaque symbol lem15711 : Prf T ≔ Tᵢ;
opaque symbol lem15712 : Prf term0 ≔ ∃ᵢ term1 T (@lem15711);
