require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1189023 [_27740 _27742 _27753] : Prf (∀ (λ f : El (fun _27740 (fun _27742 _27753)), (∀ (λ l : El (list _27740), (∀ (λ m : El (list _27742), (⇒ (= ((@LENGTH _27740) l) ((@LENGTH _27742) m)) (= ((@LENGTH _27753) ((@MAP2 _27753 _27740 _27742) f l m)) ((@LENGTH _27742) m)))))))));
