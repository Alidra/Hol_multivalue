require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3184719_term_abbrevs;
require open hol-light.thm3184708_spec;
require open hol-light.thm3184718_spec;
opaque symbol lem3184719 [_83152 _83169] : Prf (term0 _83152 _83169) ≔ ∧ᵢ (@lem3184718 _83152) (@lem3184708 _83169);
