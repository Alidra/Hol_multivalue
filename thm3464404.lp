require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464404_term_abbrevs;
require open hol-light.thm3464378_spec;
opaque symbol lem3464404 [_89711 _89725] (P : El (fun _89725 bool)) : Prf (term0 _89711 _89725 P) ≔ λ f : El (type1470 _89711 _89725), (@lem3464378 _89711 _89725 P f);
