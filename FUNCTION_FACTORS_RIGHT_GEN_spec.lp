require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3582879 [_91854 _91858 _91859] : Prf (∀ (λ P : El (fun _91859 bool), (∀ (λ f : El (fun _91859 _91854), (∀ (λ g : El (fun _91858 _91854), (= (∀ (λ x : El _91859, (⇒ (P x) (∃ (λ y : El _91858, (= (g y) (f x))))))) (∃ (λ h : El (fun _91859 _91858), (∀ (λ x : El _91859, (⇒ (P x) (= (f x) (g (h x)))))))))))))));
