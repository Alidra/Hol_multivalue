require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem6930973 [A] : Prf (∀ (λ f : El (fun A num), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (NUMERAL _0))))) (= ((@nsum A) s f) (NUMERAL _0)))))));
