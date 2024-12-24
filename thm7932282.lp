require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7932282_term_abbrevs;
opaque symbol lem7932282 [A] (a : El (type6 A)) (a' : El (type6 A)) : Prf (= (term0 A a a') (= (= ((@mktybit1 A) a) ((@mktybit1 A) a')) (= a a'))) ≔ REFL (term0 A a a');
