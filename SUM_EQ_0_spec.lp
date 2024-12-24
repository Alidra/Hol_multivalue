require open hol-light.theory_hol;
require open hol-light.hol_types;
require open hol-light.hol_terms;
symbol lem7069292 [A] : Prf (∀ (λ f : El (fun A real), (∀ (λ s : El (fun A bool), (⇒ (∀ (λ x : El A, (⇒ ((@IN A) x s) (= (f x) (real_of_num (NUMERAL _0)))))) (= ((@sum A) s f) (real_of_num (NUMERAL _0))))))));
