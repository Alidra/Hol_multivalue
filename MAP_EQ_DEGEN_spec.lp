require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1128657 [_26546] : Prf (∀ (λ l : El (list _26546), (∀ (λ f : El (fun _26546 _26546), (⇒ ((@ALL _26546) (λ x : El _26546, (= (f x) x)) l) (= ((@MAP _26546 _26546) f l) l))))));
