require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem1069365 [A] (option' : El (fun (recspace A) bool)) (NONE' : El (recspace A)) (SOME' : El (fun A (recspace A))) (h1 : Prf (= option' (λ a : El (recspace A), (∀ (λ option'' : El (fun (recspace A) bool), (⇒ (∀ (λ a' : El (recspace A), (⇒ (∨ (= a' NONE') (∃ (λ a'' : El A, (= a' (SOME' a''))))) (option'' a')))) (option'' a))))))) : Prf (∧ (∧ (option' NONE') (∀ (λ a : El A, (option' (SOME' a))))) (∧ (∀ (λ option'' : El (fun (recspace A) bool), (⇒ (∧ (option'' NONE') (∀ (λ a : El A, (option'' (SOME' a))))) (∀ (λ a : El (recspace A), (⇒ (option' a) (option'' a))))))) (∀ (λ a : El (recspace A), (= (option' a) (∨ (= a NONE') (∃ (λ a' : El A, (= a (SOME' a'))))))))));
