require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.FORALL_PASTECART_term_abbrevs;
require open hol-light.thm7660850_spec;
require open hol-light.thm7662539_spec;
opaque symbol lem7662540 [_140454 _140455 _140456] (P : El (type16 _140454 _140455 _140456)) : Prf (= (term0 _140454 _140455 _140456 P) (term1 _140454 _140455 _140456 P)) ≔ EQ_MP (@lem7660850 _140454 _140455 _140456 P) (@lem7662539 _140454 _140455 _140456 P);
