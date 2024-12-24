require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1128391 [_26528 _26529] : Prf (∀ (λ P : El (fun _26528 (fun _26529 bool)), (∀ (λ f : El (fun _26529 _26528), (∀ (λ l : El (list _26529), (= ((@ALL2 _26528 _26529) P ((@MAP _26529 _26528) f l) l) ((@ALL _26529) (λ a : El _26529, (P (f a) a)) l))))))));
