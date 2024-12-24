require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm3458942_term_abbrevs;
require open hol-light.thm3453922_spec;
require open hol-light.thm3458939_spec;
opaque symbol lem3458942 [_89646 _89670 _89671 _89672] (P : El (type1517 _89670 _89671 _89672)) (f : El (type1524 _89646 _89670 _89671 _89672)) : Prf (= (term0 _89646 _89670 _89671 _89672 P f) (term1 _89646 _89670 _89671 _89672 P f)) ≔ EQ_MP (@lem3453922 _89646 _89670 _89671 _89672 P f) (@lem3458939 _89646 _89670 _89671 _89672 P f);
