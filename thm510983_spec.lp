require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem510983 [_17370 _17371] (P : El (fun _17371 bool)) (Q : El (fun _17371 (fun _17370 bool))) : Prf (= (⇒ (¬ (= (∀ (λ x : El _17371, (⇒ (P x) (∀ (λ y : El _17370, (Q x y)))))) (∀ (λ y : El _17370, (∀ (λ x : El _17371, (⇒ (P x) (Q x y)))))))) F) (= (∀ (λ x : El _17371, (⇒ (P x) (∀ (λ y : El _17370, (Q x y)))))) (∀ (λ y : El _17370, (∀ (λ x : El _17371, (⇒ (P x) (Q x y))))))));
