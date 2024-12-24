require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1128211 [_26486 _26497] (f : El (fun _26486 _26497)) : Prf (∀ (λ l : El (list _26486), (∀ (λ m : El (list _26486), (⇒ ((@ALL2 _26486 _26486) (λ x : El _26486, (λ y : El _26486, (= (f x) (f y)))) l m) (= ((@MAP _26486 _26497) f l) ((@MAP _26486 _26497) f m)))))));
