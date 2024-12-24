require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1120972 [_26299 _26310] : Prf (∀ (λ f : El (fun _26299 _26310), (∀ (λ g : El (fun _26299 _26310), (∀ (λ l : El (list _26299), (⇒ ((@ALL _26299) (λ x : El _26299, (= (f x) (g x))) l) (= ((@MAP _26299 _26310) f l) ((@MAP _26299 _26310) g l)))))))));
