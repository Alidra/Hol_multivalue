require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3464378_term_abbrevs;
require open hol-light.thm3459041_spec;
require open hol-light.thm3464375_spec;
opaque symbol lem3464378 [_89711 _89725] (P : El (fun _89725 bool)) (f : El (type1470 _89711 _89725)) : Prf (= (term0 _89711 _89725 P f) (term1 _89711 _89725 P f)) ≔ EQ_MP (@lem3459041 _89711 _89725 P f) (@lem3464375 _89711 _89725 P f);
