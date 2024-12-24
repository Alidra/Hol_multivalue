require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm1066937_term_abbrevs;
require open hol-light.thm1066936_spec;
opaque symbol lem1066937 [A B] (sum' : El (type1333 A B)) (INL' : El (type1431 A B)) (INR' : El (type1479 A B)) (h1 : Prf (= sum' (term0 A B INL' INR'))) : Prf (term1 A B sum' INL' INR') ≔ ∧ₑ₂ (@lem1066936 A B sum' INL' INR' h1);
