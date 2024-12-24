require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3562737 [_91307 _91308] (s : El (fun _91307 bool)) : Prf (∀ (λ f : El (fun _91307 _91308), (∀ (λ t : El (fun _91308 bool), (= (∀ (λ y : El _91308, (⇒ ((@IN _91308) y t) (∃ (λ x : El _91307, (∧ ((@IN _91307) x s) (= (f x) y))))))) (∃ (λ g : El (fun _91308 _91307), (∀ (λ y : El _91308, (⇒ ((@IN _91308) y t) (∧ ((@IN _91307) (g y) s) (= (f (g y)) y))))))))))));
