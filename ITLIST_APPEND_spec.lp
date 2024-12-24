require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1129521 [_26617 _26627] : Prf (∀ (λ f : El (fun _26627 (fun _26617 _26617)), (∀ (λ a : El _26617, (∀ (λ l1 : El (list _26627), (∀ (λ l2 : El (list _26627), (= ((@ITLIST _26617 _26627) f ((@APPEND _26627) l1 l2) a) ((@ITLIST _26617 _26627) f l1 ((@ITLIST _26617 _26627) f l2 a)))))))))));
