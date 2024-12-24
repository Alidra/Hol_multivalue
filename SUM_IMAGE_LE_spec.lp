require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7197663 [A B] : Prf (∀ (λ f : El (fun A B), (∀ (λ g : El (fun B real), (∀ (λ s : El (fun A bool), (⇒ (∧ ((@FINITE A) s) (∀ (λ x : El A, (⇒ ((@IN A) x s) (real_le (real_of_num (NUMERAL _0)) (g (f x))))))) (real_le ((@sum B) ((@IMAGE A B) f s) g) ((@sum A) s ((@o A B real) g f))))))))));
