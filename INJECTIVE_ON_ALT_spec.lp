require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3560908 [_91201 _91206] : Prf (∀ (λ P : El (fun _91206 bool), (∀ (λ f : El (fun _91206 _91201), (= (∀ (λ x : El _91206, (∀ (λ y : El _91206, (⇒ (∧ (P x) (∧ (P y) (= (f x) (f y)))) (= x y)))))) (∀ (λ x : El _91206, (∀ (λ y : El _91206, (⇒ (∧ (P x) (P y)) (= (= (f x) (f y)) (= x y))))))))))));
