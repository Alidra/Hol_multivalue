require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem3581220 [_91790 _91810 _91811] : Prf (∀ (λ f : El (fun _91810 _91811), (∀ (λ g : El (fun _91810 _91790), (= (∀ (λ x : El _91810, (∀ (λ y : El _91810, (⇒ (= (g x) (g y)) (= (f x) (f y))))))) (∃ (λ h : El (fun _91790 _91811), (= f ((@o _91810 _91790 _91811) h g)))))))));
