require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066993_term_abbrevs;
require open hol-light.thm1066972_spec;
opaque symbol lem1066992 [A B] (r : El (type1677 A B)) : Prf (= r r) ≔ REFL r;
opaque symbol lem1066993 [A B] (r : El (type1677 A B)) (sum' : El (type1333 A B)) (INL' : El (type1431 A B)) (INR' : El (type1479 A B)) (h1 : Prf (= INL' (term0 A B))) (h2 : Prf (= INR' (term1 A B))) (h3 : Prf (= sum' (term2 A B INL' INR'))) : Prf (= (sum' r) (term3 A B r)) ≔ MK_COMB (@lem1066972 A B sum' INL' INR' h1 h2 h3) (@lem1066992 A B r);
