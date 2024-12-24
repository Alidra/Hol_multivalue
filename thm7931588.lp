require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
require open hol-light.hol_axioms;
require open hol-light.hol_type_abbrevs;
require open hol-light.thm7931588_term_abbrevs;
opaque symbol lem7931588 [_88266 _88270] (f : El (fun _88270 _88266)) (s : El (fun _88270 bool)) (t : El (fun _88266 bool)) : Prf (= (term0 _88266 _88270 f s t) (term1 _88266 _88270 f s t)) ≔ REFL (term0 _88266 _88270 f s t);
