require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.EXISTS_PASTECART_term_abbrevs;
require open hol-light.thm7662554_spec;
require open hol-light.thm7664352_spec;
opaque symbol lem7664353 [_140476 _140477 _140478] (P : El (type16 _140476 _140477 _140478)) : Prf (= (term0 _140476 _140477 _140478 P) (term1 _140476 _140477 _140478 P)) ≔ EQ_MP (@lem7662554 _140476 _140477 _140478 P) (@lem7664352 _140476 _140477 _140478 P);
