require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem5123225 [_114995 _114998] : Prf (∀ (λ t : El (fun _114995 bool), (∀ (λ s : El (fun _114998 bool), (= ((@=_c _114995 _114998) s t) (∃ (λ f : El (fun _114998 _114995), (∧ (∀ (λ x : El _114998, (⇒ ((@IN _114998) x s) ((@IN _114995) (f x) t)))) (∀ (λ y : El _114995, (⇒ ((@IN _114995) y t) ((@∃! _114998) (λ x : El _114998, (∧ ((@IN _114998) x s) (= (f x) y)))))))))))))));
