require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3580897 [_91760 _91764 _91765] : Prf (∀ (λ P : El (fun _91765 bool), (∀ (λ f : El (fun _91765 _91760), (∀ (λ g : El (fun _91765 _91764), (= (∀ (λ x : El _91765, (∀ (λ y : El _91765, (⇒ (∧ (P x) (∧ (P y) (= (g x) (g y)))) (= (f x) (f y))))))) (∃ (λ h : El (fun _91764 _91760), (∀ (λ x : El _91765, (⇒ (P x) (= (f x) (h (g x)))))))))))))));
